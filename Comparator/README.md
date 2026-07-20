# Comparator harness

`Challenge.lean` imports only `Mathlib` and gives each target exactly one
reviewed proof placeholder. `Solution.lean` imports the project and re-exports
a target only after its proof compiles. `config.json` lists exactly those proved
exports.

| Target ID | Planned phase | Current config status | Diagnostic purpose |
|---|---:|---|---|
| `rat_height_scaled_denominator` | P2 | present / proved | Exact rational normalization and denominator scaling |
| `weighted_log_one_add_average` | P2 | present / proved | Weighted Jensen/AM–GM estimate with degree normalization |
| `modular_delta_j_fd_comparison` | P3 | present / proved | Actual `E₄³/Δ` and `(2π)¹²Δ` fundamental-domain estimate |
| `silverman_proposition_2_1_certified` | P6 (type frozen P4) | present / proved | Expanded certificate-level headline without an arbitrary “Faltings height” |

An unproved target remains in the challenge but must not appear in the config.
The allowed logical dependencies for configured solutions are exactly
`propext`, `Quot.sound`, and `Classical.choice`.
