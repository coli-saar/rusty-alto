import pytest
from concurrent.futures import ThreadPoolExecutor

import rusty_alto as ra


GRAMMAR = r"""
interpretation string: de.up.ling.irtg.algebra.StringAlgebra
interpretation tree: de.up.ling.irtg.algebra.TreeWithAritiesAlgebra

S! -> r(NP, VP) [0.7]
  [string] *(?1, ?2)
  [tree] S_2(?1, ?2)

NP -> john [1.0]
  [string] john
  [tree] John_0

VP -> sleeps [1.0]
  [string] sleeps
  [tree] sleeps_0
"""


def test_explicit_builder_and_owner_checks():
    builder = ra.AutomatonBuilder()
    leaf = builder.add_state("leaf")
    root = builder.add_state("root", True)
    builder.add_rule("a", [], "leaf")
    builder.add_rule("f", ["leaf"], "root", 0.5)
    automaton = builder.build()

    leaf_states = automaton.step("a", [])
    assert len(leaf_states) == 1
    assert leaf_states[0].id == leaf
    assert automaton.accepts(ra.Tree("f", [ra.Tree("a")]))
    assert automaton.viterbi().weight == 0.5

    other = ra.StringAlgebra().decompose("a")
    with pytest.raises(ra.StateOwnerError):
        other.is_accepting(leaf_states[0])


def test_string_decomposition_is_lazy_and_structured():
    automaton = ra.StringAlgebra().decompose("a b")
    assert automaton.has_state_universe
    assert automaton.is_top_down
    assert automaton.is_condensed
    states = automaton.states()
    assert {(state.start, state.end) for state in states} == {
        (0, 1),
        (0, 2),
        (1, 2),
    }
    materialized, source_states = automaton.materialize()
    assert materialized.accepts(ra.Tree("*", [ra.Tree("a"), ra.Tree("b")]))
    assert source_states


def test_lazy_product_and_determinization():
    left = ra.StringAlgebra().decompose("a")
    right = ra.StringAlgebra().decompose("a")
    product = left.product(right)
    result = product.step("a", [])
    assert len(result) == 1
    assert len(result[0].components()) == 2
    assert product.is_accepting(result[0])

    deterministic = product.determinize()
    result = deterministic.step("a", [])
    assert len(result) == 1
    assert deterministic.is_accepting(result[0])


def test_tag_tree_and_binarizing_decompositions_are_lazy():
    signature = ra.Signature.from_symbols([("S", 1), ("a", 0)])
    plain = ra.TagTreeAlgebra(signature).decompose("S(a)")
    binary = ra.BinarizingTagTreeAlgebra(signature).decompose("S(a)")
    assert plain.is_top_down and plain.is_condensed
    assert binary.is_top_down and binary.is_condensed
    assert plain.initial_states()
    assert binary.initial_states()


def test_irtg_parse_decomposition_and_values():
    irtg = ra.Irtg.from_string(GRAMMAR)
    string = irtg.interpretation("string")
    decomposition = string.decompose("john sleeps")
    assert decomposition.is_condensed

    parsed = string.parse("john sleeps")
    chart = irtg.parse({"string": parsed})
    derivation = chart.best()
    assert derivation is not None
    assert derivation.weight == pytest.approx(0.7)
    values = derivation.interpret()
    assert values["string"] == "john sleeps"
    assert str(values["tree"]) == "S(John, sleeps)"


def test_cancelled_parse_returns_an_error():
    irtg = ra.Irtg.from_string(GRAMMAR)
    control = ra.ParseControl()
    control.cancel()
    assert control.is_cancelled
    with pytest.raises(ra.RustyAltoError, match="cancelled"):
        irtg.parse({"string": "john sleeps"}, control=control)


def test_shared_irtg_can_parse_from_multiple_threads():
    irtg = ra.Irtg.from_string(GRAMMAR)
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(
            pool.map(
                lambda _: irtg.best({"string": "john sleeps"}).weight,
                range(8),
            )
        )
    assert results == pytest.approx([0.7] * 8)


def test_inverse_homomorphism_stays_lazy():
    target = ra.Signature.from_symbols([("a", 0)])
    source = ra.Signature.from_symbols([("x", 0)])
    builder = ra.AutomatonBuilder()
    builder.add_state("q", True)
    builder.add_rule("a", [], "q")
    inner = builder.build()
    hom = ra.Homomorphism.from_terms(
        source, target, {source.id("x"): ra.Tree("a")}
    )
    inverse = inner.inverse_homomorphism(hom)
    assert inverse.accepts(ra.Tree("x"))
    assert inverse.has_state_universe
