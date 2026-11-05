# Ultrapower saturation proof

`CountableSaturatedExtension.lean` adapts the countable-type definitions and
nonprincipal-ultrapower diagonal argument from Elliot Glazer's
[`definable-saturated`](https://github.com/elliotglazer/definable-saturated)
repository, commit `e683bba9e758323b43dd1d6206ed2f6fc9510f06`:

- `Scotts/ModelTheory/CountableSaturation.lean`
- `Scotts/ModelTheory/CountableParameterSaturation.lean`
- `Scotts/ModelTheory/SaturatedExistence.lean`

The project was located through
[Palomar entry PALOMAR-2026-09-19-000005, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-19-000005&version=1).
The original Apache 2.0 license and NOTICE are retained in this directory.

The local adaptation changes the namespace and imports, omits unrelated
cardinality and set-theoretic applications, and connects countable partial-type
realization to this project's `MarkerBridge.SatAt`. The QE application uses
countability of the RV language and a countable elementary source submodel.
It does not use the continuum hypothesis or any forcing or arithmetic results
from the upstream project. The local compiler and axiom audit, rather than
the registry entry alone, determine whether this adaptation is verified.
