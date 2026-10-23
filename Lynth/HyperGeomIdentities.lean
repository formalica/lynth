module

import all Lynth.HGIdentities.Arcsin2F1
import all Lynth.HGIdentities.Atanh2F1
import all Lynth.HGIdentities.Bessel0F1
import all Lynth.HGIdentities.BesselI
import all Lynth.HGIdentities.Common
import all Lynth.HGIdentities.CosArcsin2F1
import all Lynth.HGIdentities.Elliptic
import all Lynth.HGIdentities.Gauss2F1
import all Lynth.HGIdentities.Hyper1F0
import all Lynth.HGIdentities.Hyper3F2
import all Lynth.HGIdentities.Hyper3F2b
import all Lynth.HGIdentities.Log2F1
import all Lynth.HGIdentities.Quadratic2F1

/-!
# Hypergeometric identities

This file collects all the hypergeometric identities proved in this project.  Each identity
lives in its own file inside `Lynth/HGIdentities/`, where the identity itself is the
only public theorem; all auxiliary results of a file are private to it.

The shared infrastructure lives outside that directory, in `Lynth.Hypergeometric`
(the classical function `Complex.HGFun`, built from Mathlib's `Complex.regularizedHGFun`),
`Lynth.ComplexFuncs` (elementary complex functions) and `Lynth.SeriesTools`
(termwise differentiation of power series), together with
`Lynth.HGIdentities.Common` (Pochhammer/Gamma manipulations and the binomial series).
-/
