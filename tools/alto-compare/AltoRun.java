import de.up.ling.irtg.automata.TreeAutomaton;
import de.up.ling.irtg.codec.TreeAutomatonInputCodec;
import de.up.ling.tree.Tree;
import de.up.ling.tree.TreeParser;
import it.unimi.dsi.fastutil.ints.IntIterable;

import java.io.ByteArrayInputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

public class AltoRun {
    public static void main(String[] args) throws Exception {
        Config config = Config.parse(args);
        String autoText = Files.readString(Path.of(config.autoFile), StandardCharsets.UTF_8);
        TreeAutomaton<?> automaton = new TreeAutomatonInputCodec()
                .read(new ByteArrayInputStream(autoText.getBytes(StandardCharsets.UTF_8)));
        List<Tree<Integer>> trees = new ArrayList<>();
        for (Tree<String> tree : readTrees(config.treeFile)) {
            trees.add(automaton.getSignature().addAllSymbols(tree));
        }

        int accepted = 0;
        int rootStates = 0;
        for (int i = 0; i < config.warmup; i++) {
            Result result = runAll(automaton, trees);
            accepted = result.accepted;
            rootStates = result.rootStates;
        }

        long start = System.nanoTime();
        for (int i = 0; i < config.iterations; i++) {
            Result result = runAll(automaton, trees);
            accepted = result.accepted;
            rootStates = result.rootStates;
        }
        long elapsed = System.nanoTime() - start;
        long runs = (long) config.iterations * trees.size();

        System.out.println("engine=alto");
        System.out.println("automaton=" + config.autoFile);
        System.out.println("trees=" + config.treeFile);
        System.out.println("tree_count=" + trees.size());
        System.out.println("iterations=" + config.iterations);
        System.out.println("runs=" + runs);
        System.out.println("accepted_last=" + accepted);
        System.out.println("root_states_last=" + rootStates);
        System.out.printf(Locale.ROOT, "elapsed_ms=%.3f%n", elapsed / 1_000_000.0);
        System.out.printf(Locale.ROOT, "ns_per_tree=%.3f%n", elapsed / (double) runs);
    }

    private static Result runAll(TreeAutomaton<?> automaton, List<Tree<Integer>> trees) {
        int accepted = 0;
        int rootStates = 0;
        for (Tree<Integer> tree : trees) {
            Set<Integer> uniqueStates = new HashSet<>();
            boolean acceptedHere = false;
            IntIterable states = automaton.runRaw(tree);
            for (int state : states) {
                uniqueStates.add(state);
                if (automaton.getFinalStates().contains(state)) {
                    acceptedHere = true;
                }
            }
            rootStates += uniqueStates.size();
            if (acceptedHere) {
                accepted++;
            }
        }
        return new Result(accepted, rootStates);
    }

    private static List<Tree<String>> readTrees(String file) throws Exception {
        List<Tree<String>> trees = new ArrayList<>();
        int lineNo = 0;
        for (String line : Files.readAllLines(Path.of(file), StandardCharsets.UTF_8)) {
            lineNo++;
            String trimmed = line.trim();
            if (trimmed.isEmpty() || trimmed.startsWith("#") || trimmed.startsWith("//")) {
                continue;
            }
            try {
                trees.add(TreeParser.parse(trimmed));
            } catch (Exception e) {
                throw new RuntimeException("Could not parse tree on line " + lineNo + ": " + trimmed, e);
            }
        }
        return trees;
    }

    private static class Result {
        final int accepted;
        final int rootStates;

        Result(int accepted, int rootStates) {
            this.accepted = accepted;
            this.rootStates = rootStates;
        }
    }

    private static class Config {
        String autoFile;
        String treeFile;
        int iterations = 100;
        int warmup = 10;

        static Config parse(String[] args) {
            Config config = new Config();
            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case "--auto":
                        config.autoFile = args[++i];
                        break;
                    case "--trees":
                        config.treeFile = args[++i];
                        break;
                    case "--iterations":
                        config.iterations = Integer.parseInt(args[++i]);
                        break;
                    case "--warmup":
                        config.warmup = Integer.parseInt(args[++i]);
                        break;
                    default:
                        throw new IllegalArgumentException("unknown argument: " + args[i] + "\n" + usage());
                }
            }
            if (config.autoFile == null || config.treeFile == null) {
                throw new IllegalArgumentException(usage());
            }
            return config;
        }

        static String usage() {
            return "usage: AltoRun --auto FILE.auto --trees TREES.txt [--iterations N] [--warmup N]";
        }
    }
}
