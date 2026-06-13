import de.up.ling.irtg.automata.ConcreteTreeAutomaton;
import de.up.ling.irtg.automata.IntersectionAutomaton;
import de.up.ling.irtg.automata.Rule;
import de.up.ling.irtg.siblingfinder.SiblingFinder;
import de.up.ling.irtg.signature.Signature;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Queue;
import java.util.Set;

public class AltoIntersectionRun {
    private static final String CONCAT = "*";

    public static void main(String[] args) {
        try {
            Config config = Config.parse(args);
            Workload workload = new Workload(config.states, config.len, config.vocab);

            Summary last = new Summary();
            for (int i = 0; i < config.warmup; i++) {
                last = run(config.algorithm, workload);
            }

            long start = System.nanoTime();
            for (int i = 0; i < config.iterations; i++) {
                last = run(config.algorithm, workload);
            }
            long elapsed = System.nanoTime() - start;

            System.out.println("engine=alto");
            System.out.println("algorithm=" + config.algorithm);
            System.out.println("grammar_states=" + config.states);
            System.out.println("sentence_len=" + config.len);
            System.out.println("vocab=" + config.vocab);
            System.out.println("iterations=" + config.iterations);
            System.out.println("warmup=" + config.warmup);
            System.out.println("left_rules=" + workload.leftRules);
            System.out.println("right_rules=" + workload.rightRules);
            System.out.println("output_states=" + last.states);
            System.out.println("output_rules=" + last.rules);
            System.out.printf(Locale.ROOT, "elapsed_ms=%.3f%n", elapsed / 1_000_000.0);
            System.out.printf(Locale.ROOT, "ns_per_intersection=%.3f%n", elapsed / (double) config.iterations);
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static Summary run(String algorithm, Workload workload) {
        switch (algorithm) {
            case "naive":
                return runNaive(workload);
            case "sibling":
                return runSibling(workload);
            default:
                throw new IllegalArgumentException("unknown algorithm: " + algorithm);
        }
    }

    private static Summary runNaive(Workload workload) {
        IntersectionAutomaton<?, ?> intersection =
                IntersectionAutomaton.intersectBottomUpNaive(workload.left, workload.right);
        Summary summary = new Summary();
        summary.rules = count(intersection.getRuleSet());
        summary.states = intersection.getAllStates().size();
        return summary;
    }

    private static Summary runSibling(Workload workload) {
        List<Rule> leftRules = toList(workload.left.getRuleSet());
        ChildIndex leftIndex = ChildIndex.build(leftRules);
        Map<Integer, SiblingFinder> rightFinders = new HashMap<>();
        for (int label = 1; label <= workload.signature.getMaxSymbolId(); label++) {
            if (workload.signature.getArity(label) >= 2) {
                rightFinders.put(label, workload.right.newSiblingFinder(label));
            }
        }

        Map<PairKey, Integer> pairs = new HashMap<>();
        Queue<PairKey> queue = new ArrayDeque<>();
        Set<OutRule> rules = new HashSet<>();

        for (Rule leftRule : leftRules) {
            if (leftRule.getArity() != 0) {
                continue;
            }
            for (Rule rightRule : workload.right.getRulesBottomUp(leftRule.getLabel(), new int[0])) {
                PairKey pair = new PairKey(leftRule.getParent(), rightRule.getParent());
                int parent = internPair(pairs, pair);
                queue.add(pair);
                rules.add(new OutRule(leftRule.getLabel(), new int[0], parent));
            }
        }

        while (!queue.isEmpty()) {
            PairKey childPair = queue.remove();
            List<Occurrence> occurrences = leftIndex.byState.get(childPair.left);
            if (occurrences == null) {
                continue;
            }

            for (Occurrence occurrence : occurrences) {
                SiblingFinder finder = rightFinders.get(occurrence.label);
                if (finder == null) {
                    continue;
                }
                finder.addState(childPair.right, occurrence.position);
                Rule leftRule = leftRules.get(occurrence.ruleIndex);

                for (int[] rightChildren : finder.getPartners(childPair.right, occurrence.position)) {
                    for (Rule rightRule : workload.right.getRulesBottomUp(occurrence.label, rightChildren)) {
                        if (leftRule.getArity() != rightRule.getArity()) {
                            continue;
                        }

                        int[] children = new int[leftRule.getArity()];
                        boolean ok = true;
                        for (int i = 0; i < children.length; i++) {
                            PairKey key = new PairKey(leftRule.getChildren()[i], rightRule.getChildren()[i]);
                            Integer child = pairs.get(key);
                            if (child == null) {
                                ok = false;
                                break;
                            }
                            children[i] = child;
                        }
                        if (!ok) {
                            continue;
                        }

                        PairKey parentPair = new PairKey(leftRule.getParent(), rightRule.getParent());
                        boolean existed = pairs.containsKey(parentPair);
                        int parent = internPair(pairs, parentPair);
                        if (!existed) {
                            queue.add(parentPair);
                        }
                        rules.add(new OutRule(occurrence.label, children, parent));
                    }
                }
            }
        }

        Summary summary = new Summary();
        summary.states = pairs.size();
        summary.rules = rules.size();
        return summary;
    }

    private static int internPair(Map<PairKey, Integer> pairs, PairKey pair) {
        Integer id = pairs.get(pair);
        if (id != null) {
            return id;
        }
        int next = pairs.size() + 1;
        pairs.put(pair, next);
        return next;
    }

    private static ConcreteTreeAutomaton<Integer> grammarAutomaton(Signature signature, int states, int vocab) {
        ConcreteTreeAutomaton<Integer> auto = new ConcreteTreeAutomaton<>(signature);
        int concat = signature.addSymbol(CONCAT, 2);
        int[] words = new int[vocab];
        for (int i = 0; i < vocab; i++) {
            words[i] = signature.addSymbol("w" + i, 0);
        }

        int[] qs = new int[states];
        for (int i = 0; i < states; i++) {
            qs[i] = auto.addState(i);
            if (i == 0) {
                auto.addFinalState(qs[i]);
            }
        }

        for (int q : qs) {
            for (int word : words) {
                auto.addRule(auto.createRule(q, word, new int[0], 1.0));
            }
        }
        for (int left = 0; left < states; left++) {
            for (int right = 0; right < states; right++) {
                int parent = (left * 31 + right * 17) % states;
                auto.addRule(auto.createRule(qs[parent], concat, new int[]{qs[left], qs[right]}, 1.0));
            }
        }
        return auto;
    }

    private static ConcreteTreeAutomaton<String> spanAutomaton(Signature signature, int len, int vocab) {
        ConcreteTreeAutomaton<String> auto = new ConcreteTreeAutomaton<>(signature);
        int concat = signature.addSymbol(CONCAT, 2);
        int[] words = new int[vocab];
        for (int i = 0; i < vocab; i++) {
            words[i] = signature.addSymbol("w" + i, 0);
        }

        int[][] spans = new int[len + 1][len + 1];
        for (int i = 0; i < len; i++) {
            for (int j = i + 1; j <= len; j++) {
                spans[i][j] = auto.addState(i + "-" + j);
            }
        }
        auto.addFinalState(spans[0][len]);

        for (int i = 0; i < len; i++) {
            auto.addRule(auto.createRule(spans[i][i + 1], words[i % vocab], new int[0], 1.0));
        }
        for (int width = 2; width <= len; width++) {
            for (int i = 0; i <= len - width; i++) {
                int j = i + width;
                for (int k = i + 1; k < j; k++) {
                    auto.addRule(auto.createRule(spans[i][j], concat, new int[]{spans[i][k], spans[k][j]}, 1.0));
                }
            }
        }
        return auto;
    }

    private static <T> int count(Iterable<T> xs) {
        int ret = 0;
        for (T ignored : xs) {
            ret++;
        }
        return ret;
    }

    private static <T> List<T> toList(Iterable<T> xs) {
        List<T> ret = new ArrayList<>();
        for (T x : xs) {
            ret.add(x);
        }
        return ret;
    }

    private static class Workload {
        final Signature signature = new Signature();
        final ConcreteTreeAutomaton<Integer> left;
        final ConcreteTreeAutomaton<String> right;
        final int leftRules;
        final int rightRules;

        Workload(int states, int len, int vocab) {
            left = grammarAutomaton(signature, states, vocab);
            right = spanAutomaton(signature, len, vocab);
            leftRules = count(left.getRuleSet());
            rightRules = count(right.getRuleSet());
        }
    }

    private static class Summary {
        int states;
        int rules;
    }

    private static class Occurrence {
        final int label;
        final int position;
        final int ruleIndex;

        Occurrence(int label, int position, int ruleIndex) {
            this.label = label;
            this.position = position;
            this.ruleIndex = ruleIndex;
        }
    }

    private static class ChildIndex {
        final Map<Integer, List<Occurrence>> byState = new HashMap<>();

        static ChildIndex build(List<Rule> rules) {
            ChildIndex index = new ChildIndex();
            for (int ruleIndex = 0; ruleIndex < rules.size(); ruleIndex++) {
                Rule rule = rules.get(ruleIndex);
                int[] children = rule.getChildren();
                for (int position = 0; position < children.length; position++) {
                    index.byState
                            .computeIfAbsent(children[position], ignored -> new ArrayList<>())
                            .add(new Occurrence(rule.getLabel(), position, ruleIndex));
                }
            }
            return index;
        }
    }

    private static class PairKey {
        final int left;
        final int right;

        PairKey(int left, int right) {
            this.left = left;
            this.right = right;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof PairKey)) {
                return false;
            }
            PairKey other = (PairKey) o;
            return left == other.left && right == other.right;
        }

        @Override
        public int hashCode() {
            return 31 * left + right;
        }
    }

    private static class OutRule {
        final int label;
        final int[] children;
        final int parent;

        OutRule(int label, int[] children, int parent) {
            this.label = label;
            this.children = children.clone();
            this.parent = parent;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof OutRule)) {
                return false;
            }
            OutRule other = (OutRule) o;
            return label == other.label
                    && parent == other.parent
                    && java.util.Arrays.equals(children, other.children);
        }

        @Override
        public int hashCode() {
            return Objects.hash(label, parent, java.util.Arrays.hashCode(children));
        }
    }

    private static class Config {
        String algorithm = "sibling";
        int states = 16;
        int len = 12;
        int vocab = 4;
        int iterations = 100;
        int warmup = 10;

        static Config parse(String[] args) {
            Config config = new Config();
            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case "--algorithm":
                        config.algorithm = args[++i];
                        break;
                    case "--states":
                        config.states = Integer.parseInt(args[++i]);
                        break;
                    case "--len":
                        config.len = Integer.parseInt(args[++i]);
                        break;
                    case "--vocab":
                        config.vocab = Integer.parseInt(args[++i]);
                        break;
                    case "--iterations":
                        config.iterations = Integer.parseInt(args[++i]);
                        break;
                    case "--warmup":
                        config.warmup = Integer.parseInt(args[++i]);
                        break;
                    case "-h":
                    case "--help":
                        System.out.println(usage());
                        System.exit(0);
                        break;
                    default:
                        throw new IllegalArgumentException("unknown argument: " + args[i] + "\n" + usage());
                }
            }
            if (!config.algorithm.equals("naive") && !config.algorithm.equals("sibling")) {
                throw new IllegalArgumentException("algorithm must be naive or sibling");
            }
            return config;
        }

        static String usage() {
            return "usage: AltoIntersectionRun --algorithm naive|sibling [--states N] [--len N] [--vocab N] [--iterations N] [--warmup N]";
        }
    }
}
