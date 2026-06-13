import de.up.ling.irtg.algebra.StringAlgebra;
import de.up.ling.irtg.automata.ConcreteTreeAutomaton;
import de.up.ling.irtg.automata.Rule;
import de.up.ling.irtg.automata.TreeAutomaton;
import de.up.ling.irtg.automata.condensed.CondensedNondeletingInverseHomAutomaton;
import de.up.ling.irtg.automata.condensed.CondensedTreeAutomaton;
import de.up.ling.irtg.hom.Homomorphism;
import de.up.ling.irtg.hom.HomomorphismSymbol;
import de.up.ling.irtg.signature.Signature;
import de.up.ling.tree.Tree;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

public class AltoCondensedParsingRun {
    private static final String CONCAT = "*";

    public static void main(String[] args) {
        try {
            Config config = Config.parse(args);
            Workload workload = new Workload(
                    config.states,
                    config.len,
                    config.vocab,
                    config.lexicalLabels,
                    config.binaryLabels);

            Summary last = new Summary();
            for (int i = 0; i < config.warmup; i++) {
                last = run(workload);
            }

            long start = System.nanoTime();
            for (int i = 0; i < config.iterations; i++) {
                last = run(workload);
            }
            long elapsed = System.nanoTime() - start;

            System.out.println("engine=alto");
            System.out.println("algorithm=condensed-invhom");
            System.out.println("grammar_states=" + config.states);
            System.out.println("sentence_len=" + config.len);
            System.out.println("vocab=" + config.vocab);
            System.out.println("lexical_labels=" + config.lexicalLabels);
            System.out.println("binary_labels=" + config.binaryLabels);
            System.out.println("iterations=" + config.iterations);
            System.out.println("warmup=" + config.warmup);
            System.out.println("grammar_rules=" + workload.grammarRules);
            System.out.println("decomp_rules=" + workload.decompRules);
            System.out.println("condensed_rules_last=NA");
            System.out.println("output_states=" + last.states);
            System.out.println("output_rules=" + last.rules);
            System.out.printf(Locale.ROOT, "elapsed_ms=%.3f%n", elapsed / 1_000_000.0);
            System.out.printf(Locale.ROOT, "ns_per_parse=%.3f%n", elapsed / (double) config.iterations);
        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static Summary run(Workload workload) {
        TreeAutomaton<?> intersection = workload.grammar.intersectCondensed(workload.condensedInvhom);
        intersection.makeAllRulesExplicit();
        Summary summary = new Summary();
        summary.rules = count(intersection.getRuleSet());
        summary.states = intersection.getAllStates().size();
        return summary;
    }

    private static ConcreteTreeAutomaton<Integer> grammarAutomaton(
            Signature signature,
            int states,
            int vocab,
            int lexicalLabels,
            int binaryLabels) {
        ConcreteTreeAutomaton<Integer> auto = new ConcreteTreeAutomaton<>(signature);
        int[] qs = new int[states];
        for (int i = 0; i < states; i++) {
            qs[i] = auto.addState(i);
            if (i == 0) {
                auto.addFinalState(qs[i]);
            }
        }

        for (int q : qs) {
            for (int word = 0; word < vocab; word++) {
                for (int variant = 0; variant < lexicalLabels; variant++) {
                    int label = signature.addSymbol(lexName(word, variant), 0);
                    auto.addRule(auto.createRule(q, label, new int[0], 1.0));
                }
            }
        }

        for (int op = 0; op < binaryLabels; op++) {
            int label = signature.addSymbol(binName(op), 2);
            for (int left = 0; left < states; left++) {
                for (int right = 0; right < states; right++) {
                    int parent = (left * 31 + right * 17 + op * 13) % states;
                    auto.addRule(auto.createRule(qs[parent], label, new int[]{qs[left], qs[right]}, 1.0));
                }
            }
        }

        return auto;
    }

    private static Homomorphism stringHomomorphism(
            Signature sourceSignature,
            Signature targetSignature,
            int vocab,
            int lexicalLabels,
            int binaryLabels) {
        Homomorphism hom = new Homomorphism(sourceSignature, targetSignature);
        int concat = targetSignature.addSymbol(CONCAT, 2);

        for (int word = 0; word < vocab; word++) {
            int targetWord = targetSignature.addSymbol(wordName(word), 0);
            Tree<HomomorphismSymbol> rhs =
                    Tree.create(HomomorphismSymbol.createConstant(targetWord));
            for (int variant = 0; variant < lexicalLabels; variant++) {
                hom.add(sourceSignature.getIdForSymbol(lexName(word, variant)), rhs);
            }
        }

        Tree<HomomorphismSymbol> concatRhs = Tree.create(
                HomomorphismSymbol.createConstant(concat),
                Tree.create(HomomorphismSymbol.createVariable(0)),
                Tree.create(HomomorphismSymbol.createVariable(1)));
        for (int op = 0; op < binaryLabels; op++) {
            hom.add(sourceSignature.getIdForSymbol(binName(op)), concatRhs);
        }

        return hom;
    }

    private static List<String> sentence(int len, int vocab) {
        List<String> words = new ArrayList<>();
        for (int i = 0; i < len; i++) {
            words.add(wordName(i % vocab));
        }
        return words;
    }

    private static String wordName(int word) {
        return "w" + word;
    }

    private static String lexName(int word, int variant) {
        return "lex_" + word + "_" + variant;
    }

    private static String binName(int op) {
        return "bin_" + op;
    }

    private static <T> int count(Iterable<T> xs) {
        int ret = 0;
        for (T ignored : xs) {
            ret++;
        }
        return ret;
    }

    private static class Workload {
        final Signature sourceSignature = new Signature();
        final StringAlgebra algebra = new StringAlgebra();
        final ConcreteTreeAutomaton<Integer> grammar;
        final CondensedTreeAutomaton<?> condensedInvhom;
        final int grammarRules;
        final int decompRules;

        Workload(int states, int len, int vocab, int lexicalLabels, int binaryLabels) {
            grammar = grammarAutomaton(sourceSignature, states, vocab, lexicalLabels, binaryLabels);
            Homomorphism hom = stringHomomorphism(
                    sourceSignature,
                    algebra.getSignature(),
                    vocab,
                    lexicalLabels,
                    binaryLabels);
            TreeAutomaton<?> decomp = algebra.decompose(sentence(len, vocab));
            condensedInvhom = new CondensedNondeletingInverseHomAutomaton<>(decomp, hom);
            grammarRules = count(grammar.getRuleSet());
            decomp.makeAllRulesExplicit();
            decompRules = count(decomp.getRuleSet());
        }
    }

    private static class Summary {
        int states;
        int rules;
    }

    private static class Config {
        int states = 16;
        int len = 12;
        int vocab = 4;
        int lexicalLabels = 4;
        int binaryLabels = 16;
        int iterations = 10;
        int warmup = 2;

        static Config parse(String[] args) {
            Config config = new Config();
            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case "--states":
                        config.states = parsePositive(args, ++i, "--states");
                        break;
                    case "--len":
                        config.len = parsePositive(args, ++i, "--len");
                        break;
                    case "--vocab":
                        config.vocab = parsePositive(args, ++i, "--vocab");
                        break;
                    case "--lexical-labels":
                        config.lexicalLabels = parsePositive(args, ++i, "--lexical-labels");
                        break;
                    case "--binary-labels":
                        config.binaryLabels = parsePositive(args, ++i, "--binary-labels");
                        break;
                    case "--iterations":
                        config.iterations = parsePositive(args, ++i, "--iterations");
                        break;
                    case "--warmup":
                        config.warmup = parseNonnegative(args, ++i, "--warmup");
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
            return config;
        }

        private static int parsePositive(String[] args, int index, String name) {
            int value = parseInt(args, index, name);
            if (value <= 0) {
                throw new IllegalArgumentException(name + " must be positive");
            }
            return value;
        }

        private static int parseNonnegative(String[] args, int index, String name) {
            int value = parseInt(args, index, name);
            if (value < 0) {
                throw new IllegalArgumentException(name + " must be nonnegative");
            }
            return value;
        }

        private static int parseInt(String[] args, int index, String name) {
            if (index >= args.length) {
                throw new IllegalArgumentException("missing value for " + name + "\n" + usage());
            }
            return Integer.parseInt(args[index]);
        }
    }

    private static String usage() {
        return "usage: AltoCondensedParsingRun [--states N] [--len N] [--vocab N] [--lexical-labels N] [--binary-labels N] [--iterations N] [--warmup N]";
    }
}
