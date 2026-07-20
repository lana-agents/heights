# Comparator harness

`Challenge.lean` imports only `Mathlib` and gives each target exactly one
reviewed proof placeholder. `Solution.lean` also imports only `Mathlib`; a
project result is copied or re-exported there only after it has been proved.
`config.json` lists only those proved exports, so both name arrays are empty in
P1.

| Target ID | Planned phase | Config status in P1 | Diagnostic purpose |
|---|---:|---|---|
| `rat_height_scaled_denominator` | P2 | absent / not proved | Exact rational normalization and denominator scaling |
| `weighted_log_one_add_average` | P2 | absent / not proved | Weighted Jensen/AM–GM estimate with degree normalization |
| `modular_delta_j_fd_comparison` | P3 | absent / not proved | Actual `E₄³/Δ` and `(2π)¹²Δ` fundamental-domain estimate |
| `silverman_proposition_2_1_certified` | P6 (type frozen P4) | absent / not proved | Expanded certificate-level headline without an arbitrary “Faltings height” |

An unproved target remains in the challenge but must not appear in the config.
The allowed logical dependencies for configured solutions are exactly
`propext`, `Quot.sound`, and `Classical.choice`.
