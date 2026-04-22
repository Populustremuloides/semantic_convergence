/-
Top-level import surface for the project.

The concrete `Concrete*` modules are the active first-principles foundation.
The paper-facing theorem modules remain imported for their canonical wrapper
names; any retained abstract `...Model` / `...Theory` APIs inside those files
are legacy compatibility scaffolding only and are not part of the active trust
boundary.
-/

import AlgorithmicFreeEnergy.Foundations
import AlgorithmicFreeEnergy.ConcreteCore
import AlgorithmicFreeEnergy.ConcretePrior
import AlgorithmicFreeEnergy.ConcreteHierarchy
import AlgorithmicFreeEnergy.ConcreteFunctional
import AlgorithmicFreeEnergy.ConcreteBelief
import AlgorithmicFreeEnergy.ConcreteSemantic
import AlgorithmicFreeEnergy.ConcreteRates
import AlgorithmicFreeEnergy.ConcreteNoise
import AlgorithmicFreeEnergy.ConcreteSelfReference
import AlgorithmicFreeEnergy.ConcreteBoundary
import AlgorithmicFreeEnergy.ConcreteSurrogate
import AlgorithmicFreeEnergy.Hierarchy
import AlgorithmicFreeEnergy.Functional
import AlgorithmicFreeEnergy.Belief
import AlgorithmicFreeEnergy.Semantic
import AlgorithmicFreeEnergy.Noise
import AlgorithmicFreeEnergy.Rates
import AlgorithmicFreeEnergy.SelfReference
import AlgorithmicFreeEnergy.Boundary
import AlgorithmicFreeEnergy.Surrogate
import AlgorithmicFreeEnergy.Manifest
