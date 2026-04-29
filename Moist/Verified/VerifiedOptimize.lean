import Moist.Verified.ANFSoundness
import Moist.Verified.DCESoundness
import Moist.Verified.InlineSoundness

/-! # Verified Optimization Pipeline

Composes ANF normalization, dead code elimination, and inlining into a
single optimization pass with an end-to-end soundness proof.

    verifiedOptimize = anfNormalize ; dce ; inlinePassWithCanon
-/

namespace Moist.Verified.MIR

open Moist.MIR (Expr FreshState anfNormalize dce inlinePassWithCanon)

instance : Trans MIRCtxRefines MIRCtxRefines MIRCtxRefines where
  trans := mirCtxRefines_trans

def verifiedOptimize (e : Expr) (s : FreshState) : Expr × FreshState :=
  let (anf, s₁) := anfNormalize e s
  let (dced, _) := dce anf
  let ((inlined, _), s₂) := inlinePassWithCanon dced s₁
  (inlined, s₂)

theorem verifiedOptimize_refines (e : Expr) (s : FreshState) :
    e ⊑Ctxᴹ (verifiedOptimize e s).1 := by
  unfold verifiedOptimize
  let anf := (anfNormalize e s)
  let dced := (dce anf.1)
  calc e    ⊑Ctxᴹ anf.1  := anfNormalize_refines e s
       _    ⊑Ctxᴹ dced.1 := dce_refines anf.1
       _    ⊑Ctxᴹ _    := inline_refines dced.1 anf.2

end Moist.Verified.MIR
