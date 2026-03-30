//Imorts
import java.io.BufferedInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;

/**
 * Policy-Based Link State Routing with Gateway Constraints
 * 
 * This program implements a routing algorithm where:
 * - Regular nodes can only route through other regular nodes
 * - Gateways are destinations but cannot be used as intermediate hops
 * - All traffic must pass through a designated Source Area (SA) node
 * 
 * The algorithm uses Dijkstra's algorithm with gateway blocking to compute:
 * 1. Shortest paths from any node to the SA
 * 2. Shortest paths from the SA to all gateways
 * 3. Combines these to create forwarding tables for each regular node
 */
public class RouteToGateway {
    // Infinity constant for Dijkstra's algorithm - using MAX_VALUE/4 to prevent overflow
    private static final long INF = Long.MAX_VALUE / 4;

    /**
     * Fast input scanner for reading integers efficiently
     * Uses buffered I/O and manual parsing for better performance than Scanner
     */
    private static class FastScanner {
        private final BufferedInputStream in = new BufferedInputStream(System.in);
        private final byte[] buffer = new byte[1 << 16];
        private int ptr = 0;
        private int len = 0;

        private int read() throws IOException {
            if (ptr >= len) {
                len = in.read(buffer);
                ptr = 0;
                if (len <= 0) return -1;
            }
            return buffer[ptr++];
        }

        Integer nextInt() throws IOException {
            int c;
            do {
                c = read();
                if (c == -1) return null;
            } while (c <= ' ');

            int sign = 1;
            if (c == '-') {
                sign = -1;
                c = read();
            }

            int val = 0;
            while (c > ' ') {
                val = val * 10 + (c - '0');
                c = read();
            }
            return sign * val;
        }
    }

    private static class Edge {
        int to;
        int w;

        Edge(int to, int w) {
            this.to = to;
            this.w = w;
        }
    }

    private static class State implements Comparable<State> {
        int node;
        long dist;

        State(int node, long dist) {
            this.node = node;
            this.dist = dist;
        }

        @Override
        public int compareTo(State other) {
            return Long.compare(this.dist, other.dist);
        }
    }

    private static class DijkstraResult {
        long[] dist;
        List<Integer>[] parents;

        DijkstraResult(long[] dist, List<Integer>[] parents) {
            this.dist = dist;
            this.parents = parents;
        }
    }

    @SuppressWarnings("unchecked")
    private static DijkstraResult dijkstraWithGatewayBlocking(
            List<Edge>[] graph,
            int start,
            Set<Integer> gateways
    ) {
        int n = graph.length - 1;
        long[] dist = new long[n + 1];
        Arrays.fill(dist, INF);
        List<Integer>[] parents = new ArrayList[n + 1];
        for (int i = 1; i <= n; i++) {
            parents[i] = new ArrayList<>();
        }

        PriorityQueue<State> pq = new PriorityQueue<>();
        dist[start] = 0;
        pq.add(new State(start, 0));

        while (!pq.isEmpty()) {
            State cur = pq.poll();
            int u = cur.node;
            if (cur.dist != dist[u]) continue;

            // Gateways are allowed as destinations, but never as intermediates.
            // So we do not expand from gateways (except the start node itself).
            if (u != start && gateways.contains(u)) continue;

            for (Edge e : graph[u]) {
                int v = e.to;
                long nd = dist[u] + e.w;
                if (nd < dist[v]) {
                    dist[v] = nd;
                    parents[v].clear();
                    parents[v].add(u);
                    pq.add(new State(v, nd));
                } else if (nd == dist[v]) {
                    parents[v].add(u);
                }
            }
        }

        return new DijkstraResult(dist, parents);
    }

    private static List<Integer> sortedUnique(List<Integer> list) {
        if (list.isEmpty()) return list;
        Collections.sort(list);
        List<Integer> out = new ArrayList<>();
        int prev = Integer.MIN_VALUE;
        for (int x : list) {
            if (x != prev) out.add(x);
            prev = x;
        }
        return out;
    }

    private static List<Integer> firstHopsFromSA(
            int target,
            int sa,
            List<Integer>[] parents,
            List<Integer>[] memo,
            boolean[] computed,
            boolean[] visiting
    ) {
        if (computed[target]) return memo[target];
        if (visiting[target]) return new ArrayList<>();

        visiting[target] = true;
        List<Integer> hops = new ArrayList<>();

        for (int p : parents[target]) {
            if (p == sa) {
                hops.add(target);
            } else {
                hops.addAll(firstHopsFromSA(p, sa, parents, memo, computed, visiting));
            }
        }

        visiting[target] = false;
        computed[target] = true;
        memo[target] = sortedUnique(hops);
        return memo[target];
    }

    private static String joinInts(List<Integer> nums) {
        if (nums == null || nums.isEmpty()) return "-1";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < nums.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(nums.get(i));
        }
        return sb.toString();
    }

    public static void main(String[] args) throws Exception {
        FastScanner fs = new FastScanner();

        Integer nObj = fs.nextInt();
        if (nObj == null) return;
        int n = nObj;

        @SuppressWarnings("unchecked")
        List<Edge>[] graph = new ArrayList[n + 1];
        @SuppressWarnings("unchecked")
        List<Edge>[] reversed = new ArrayList[n + 1];
        for (int i = 1; i <= n; i++) {
            graph[i] = new ArrayList<>();
            reversed[i] = new ArrayList<>();
        }

        int[][] matrix = new int[n + 1][n + 1];
        for (int i = 1; i <= n; i++) {
            for (int j = 1; j <= n; j++) {
                Integer wObj = fs.nextInt();
                if (wObj == null) return;
                matrix[i][j] = wObj;
            }
        }

        List<Integer> gateways = new ArrayList<>();
        for (int i = 1; i <= n; i++) {
            if (matrix[i][i] == -1) continue; // no-op; just keeps parser deterministic
        }

        // Gateways are provided as space-separated indices.
        // Since input shape is fixed, we read tokens of this line indirectly:
        // all remaining ints except the final one (SA) are gateways.
        // To support this, we first gather all remaining ints.
        List<Integer> rest = new ArrayList<>();
        Integer tok;
        while ((tok = fs.nextInt()) != null) {
            rest.add(tok);
        }
        if (rest.isEmpty()) return;
        int sa = rest.get(rest.size() - 1);
        for (int i = 0; i < rest.size() - 1; i++) {
            gateways.add(rest.get(i));
        }
        Collections.sort(gateways);

        Set<Integer> gatewaySet = new HashSet<>(gateways);

        // Build graph and transposed graph from adjacency matrix.
        // -1 means no edge. Self loops are ignored for routing.
        for (int i = 1; i <= n; i++) {
            for (int j = 1; j <= n; j++) {
                int w = matrix[i][j];
                if (w < 0 || i == j) continue;
                graph[i].add(new Edge(j, w));
                reversed[j].add(new Edge(i, w));
            }
        }

        // 1) Dist from any node to SA in original graph:
        // run Dijkstra from SA on transposed graph.
        DijkstraResult toSA = dijkstraWithGatewayBlocking(reversed, sa, gatewaySet);

        // 2) Dist from SA to gateways in original graph.
        DijkstraResult fromSA = dijkstraWithGatewayBlocking(graph, sa, gatewaySet);

        @SuppressWarnings("unchecked")
        List<Integer>[] memoFirstHops = new ArrayList[n + 1];
        boolean[] computed = new boolean[n + 1];
        boolean[] visiting = new boolean[n + 1];

        StringBuilder out = new StringBuilder();
        boolean firstTable = true;

        for (int s = 1; s <= n; s++) {
            if (gatewaySet.contains(s)) continue;

            if (!firstTable) out.append('\n');
            firstTable = false;

            out.append("Forwarding Table for ").append(s).append('\n');
            out.append("To Cost Next Hop").append('\n');

            for (int g : gateways) {
                long cost;
                String nextHopStr;

                if (s == sa) {
                    if (fromSA.dist[g] >= INF) {
                        cost = -1;
                        nextHopStr = "-1";
                    } else {
                        cost = fromSA.dist[g];
                        List<Integer> firstHops = firstHopsFromSA(
                                g, sa, fromSA.parents, memoFirstHops, computed, visiting
                        );
                        nextHopStr = joinInts(firstHops);
                    }
                } else {
                    if (toSA.dist[s] >= INF || fromSA.dist[g] >= INF) {
                        cost = -1;
                        nextHopStr = "-1";
                    } else {
                        cost = toSA.dist[s] + fromSA.dist[g];
                        List<Integer> hops = sortedUnique(new ArrayList<>(toSA.parents[s]));
                        nextHopStr = joinInts(hops);
                    }
                }

                out.append(g).append(' ')
                        .append(cost)
                        .append(' ')
                        .append(nextHopStr)
                        .append('\n');
            }
        }

        System.out.print(out);
    }
}
