/-
Copyright (c) 2026 triviality-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: triviality-lean contributors
-/
import Triviality.Basic
import Triviality.Probability
import Triviality.Lewis
import Triviality.Fitelson
import Triviality.Pairs
import Triviality.KhooMandelkern
import Triviality.Bradley
import Triviality.TwoWays
import Triviality.Routes.GoldsteinSantorio
import Triviality.Routes.SequenceSemantics
import Triviality.Routes.StalnakerBernoulli
import Triviality.Countermodels.Fin4
import Triviality.Countermodels.Lewis
import Triviality.Countermodels.Fitelson
import Triviality.Countermodels.KhooMandelkern
import Triviality.Countermodels.Bradley

/-!
# Triviality results for the probability of conditionals

The library `Triviality` formalizes the Lewis-style triviality results for conditionals as
theorems about an arbitrary conditional operator on propositions over a finite credence space.
This root imports the library, its countermodels, the two-ways theorem and the route models.
-/
