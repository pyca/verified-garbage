module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcSetup
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcBase
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps

/-!
# The checks of an RSA key on PPC64LE: from the set-up to the mask

`prep_ok`: `setup` and `e`'s array; `Stg.base`: the checks keep `KBase`;
`ret_ok`: the mask returned.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Proof.Rsa.KeyWorkspace (arr S num slot Arrs upd upd_ne upd_self)

/-- `setup` and `e`'s array. -/
theorem prep_ok {s0 s : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na) (h : KBase B Z s0 s)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 K) {E : Nat} (h24 : s.gpr .r24 = BitVec.ofNat 64 E <<< 31)
    (hE : E < 2 ^ 33) {rest : List (Prog isa)} (hrest : rest ≠ []) {Q : State → Prop}
    (k : ∀ t, LdS B Z K s0 (upd (fun _ => 0) aE E) t → Keep (.r29 :: .r30 :: opRegs) s t →
      WP isa (Impl.Rsa.PPC64LE.Keys.seqs rest) t Q) :
    WP isa (Impl.Rsa.PPC64LE.Keys.seqs (setup :: .block eArr :: rest)) s Q := by
  obtain ⟨-, hw16, -, -⟩ := hp.ws
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (setup_ok hp h h15) fun t1 ⟨b1, w1, z1, k1⟩ => ?_
  rw [wp_seqs_cons hrest]
  have l1 := LdS.of_setup b1 w1 z1
  refine WP.mono (eArr_ok l1 (by omega) rfl (by rw [k1.gpr _ (by decide)]; exact h24) hE)
    fun t ⟨lt, kt⟩ => k t lt ((k1.trans kt).mono)

/-- The checks keep `KBase`. -/
theorem Stg.base {g : Geo} {s0 sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) (hb : KBase g.B g.Z s0 sS) (hnw : g.B.toNat + g.Z ≤ 2 ^ 64) :
    KBase g.B g.Z s0 t :=
  hb.of_keep h.keep hnw (fun j hj => h.ws.arr_fit (List.mem_range.mp hj)) (by decide) h.ws.hdr_le h.regs

/-- `ret`: the mask's bit in `r3`. -/
theorem ret_ok {g : Geo} {sS t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g sS A live c t) :
    WP isa (.block ret) t fun u => (u.gpr .r3 = BitVec.ofNat 64 (if c then 1 else 0) ∧ u.mem = t.mem) ∧
      Keep [.r3] t u := by
  have hs := h.ws.scr
  have hz := h.ws.hdr_le
  refine WP.keep _ ?_ (by decide)
  prun [Impl.Rsa.PPC64LE.KeyCheck.ret, h.ws.r31,
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide),
    hs.ld (d := sMask) (n := 4) (by unfold sMask; simp only [KeyWorkspace.hdr] at hz; omega),
    CrtValues.ofNat_slot _ h.mask]

end VG.Proof.Rsa.PPC64LE.KeyCheck
