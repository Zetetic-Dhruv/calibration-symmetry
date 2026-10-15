# Calibration as Symmetry

Lean 4 formalization for the extended abstract *Calibration as Symmetry: What a
Brain–Computer Interface Can Decode* (AI4BCI 2026).

A session records a subject through a configuration the decoder cannot see (gains, coupling,
placement, drift). Calibration items are recordings made in the same session whose latent is a
known function of the subject's latent: a physical phantom (constant), a cued trial, or a known
intervention. The file proves which targets one decoder can recover across sessions, and what
each kind of item adds.

## Results

General statements (`BCIMetrology`):

| Lean name | Statement |
|---|---|
| `decodable_iff` | A target is decodable iff any two (session, latent) pairs that reveal the same laws carry the same target. |
| `not_decodable_chance` | Otherwise, for some pair, any measurable decoder on all session data succeeds with probabilities summing to at most one. |
| `not_decodable_two_point` | Metric form: the two expected errors sum to at least the distance between the targets. |
| `decodable_group_iff` | With a calibration group acting on recordings, decodability reduces to agreement on latents related by a group element that also maps each item's law to its counterpart. |
| `Decodable.identifiable` | Phantoms do not make a non-identifiable target decodable. |
| `decodable_of_base` | Phantoms whose joint stabilizer fixes all laws make all identifiable targets decodable. |
| `Decodable.add_items`, `Decodable.mono_group` | More items, or a smaller calibration group, keep a decodable target decodable. |

Optical instance (`BCIMetrology.Windkessel`): flow and volume phasors on a two-element
Windkessel, `V = Q / (iω + 1/τ)`, `τ = RC`, recorded through channel gains `a, b` and a leak `β`
of volume into the flow channel.

| Calibration | Phantoms needed for `τ` | Lean names |
|---|---|---|
| real gains, no leak (one sensor) | 0 | `tau_zero_calibration` |
| complex gains (relative delay) | 1 | `tau_not_zero_calibration_delay`, `tau_one_phantom_delay` |
| real gains and real leak | 1 | `tau_not_zero_calibration_leak`, `tau_one_phantom_leak` |
| complex gains and leak | 2 (distinct `τ`) | `tau_not_zero_calibration_full`, `tau_not_one_phantom`, `tau_two_phantoms` |

Compliance `C` is not decodable under any calibration group with any set of phantoms
(`compliance_not_decodable`, `compliance_chance`); a recording after a known change of resistance
makes it decodable (`compliance_decodable_with_intervention`).

All statements depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

## Build

Lean v4.31.0 with Mathlib v4.31.0:

```
lake exe cache get
lake build
```

## Author

Dhruv Gupta, ARTPARK, Indian Institute of Science.
