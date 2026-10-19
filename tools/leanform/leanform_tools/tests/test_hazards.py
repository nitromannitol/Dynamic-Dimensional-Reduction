"""Tests for the probability-lint gate.

The early classes pin false positives this gate actually produced against
real repos, which two independent model runs also produced. A junk-value gate that cries wolf on `(2 : ℂ)⁻¹` gets switched off.
"""

import unittest

from leanform_tools.check_hazards import classify, scan_block


def names(text):
    return [h[0] for h in scan_block(text)]


class TestLiteralInverseIsNotAHazard(unittest.TestCase):
    """Literal inverses such as `(2 : ℂ)⁻¹` are harmless and must not be flagged."""

    def test_typed_literal_inverse_ignored(self):
        self.assertEqual(names("(2 : ℂ)⁻¹ •"), [])

    def test_nested_typed_literal_inverse_ignored(self):
        self.assertEqual(
            names("(((2 : ℂ)⁻¹ * Complex.exp (-Complex.I * p i)) *"), []
        )

    def test_bare_numeral_inverse_ignored(self):
        self.assertEqual(names("2⁻¹"), [])

    def test_unspaced_typed_literal_ignored(self):
        self.assertEqual(names("(3:ℝ)⁻¹"), [])

    def test_a_real_variable_inverse_is_still_caught(self):
        self.assertEqual(names("x⁻¹"), ["inv"])

    def test_a_compound_inverse_is_still_caught(self):
        self.assertEqual(names("(a + b)⁻¹"), ["inv"])

    def test_a_projection_inverse_is_still_caught(self):
        """A projection inverse such as `M.delta⁻¹` is a genuine hazard."""
        self.assertEqual(names("M.delta⁻¹"), ["inv"])


class TestLintegralIsNotBochner(unittest.TestCase):
    """The lower Lebesgue integral `∫⁻` is total on ℝ≥0∞, so it is not a hazard."""

    def test_lintegral_ignored(self):
        self.assertEqual(names("(∫⁻ N in B, K N A ∂Q) = Q (A ∩ B)"), [])

    def test_bochner_integral_caught(self):
        self.assertEqual(names("∫ x, f x ∂μ"), ["bochner"])


class TestWholeIdentifierMatching(unittest.TestCase):
    """Whole identifiers only: `sInf` inside `IsInfPath` is not a hit."""

    def test_sinf_inside_isinfpath_ignored(self):
        self.assertEqual(names("¬ ∃ x : ℕ → V, IsInfPath G x ∧ IsInfLive π ρ x"), [])

    def test_sinf_inside_hasinfinitecomponent_ignored(self):
        self.assertEqual(names("Sandpile.HasInfiniteComponent s"), [])

    def test_a_real_sinf_is_caught(self):
        self.assertIn("sInf", names("sInf {t | x ∈ A t}"))

    def test_ncard_caught_and_encard_not(self):
        self.assertIn("ncard", names("(S ω).ncard ≤ 2"))
        self.assertEqual(names("(S ω).encard ≤ 2"), [])


class TestClassify(unittest.TestCase):
    def test_integrable_clause_guards_a_bochner_integral(self):
        body = "theorem t (h : Integrable f μ) : ∫ x, f x ∂μ = 0 :="
        self.assertEqual(classify(body, "bochner"), "GUARDED")

    def test_enat_carrier_absorbs_an_sinf(self):
        body = "theorem t : sInf {n : ℕ∞ | p n} = ⊤ :="
        self.assertEqual(classify(body, "sInf"), "CARRIER")

    def test_a_carrier_does_not_excuse_a_division(self):
        """ℕ∞ in the block says nothing about a real division elsewhere."""
        body = "theorem t (x : ℕ∞) : f y / g y = 0 :="
        self.assertEqual(classify(body, "inv"), "UNGUARDED")

    def test_no_clause_at_all_is_unguarded(self):
        self.assertEqual(classify("theorem t : f x⁻¹ = 0 :=", "inv"), "UNGUARDED")


if __name__ == "__main__":
    unittest.main()
