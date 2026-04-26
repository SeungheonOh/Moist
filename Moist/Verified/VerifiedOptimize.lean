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

def verifiedOptimize (e : Expr) (s : FreshState) : Expr × FreshState :=
  let (anf, s₁) := anfNormalize e s
  let (dced, _) := dce anf
  let ((inlined, _), s₂) := inlinePassWithCanon dced s₁
  (inlined, s₂)

theorem verifiedOptimize_sound (e : Expr) (s : FreshState) :
    MIRCtxRefines e (verifiedOptimize e s).1 :=
  mirCtxRefines_trans
    (anfNormalize_refines e s)
    (mirCtxRefines_trans
      (dce_mirCtxRefines (anfNormalize e s).1)
      (inline_soundness (dce (anfNormalize e s).1).1 (anfNormalize e s).2))

end Moist.Verified.MIR
