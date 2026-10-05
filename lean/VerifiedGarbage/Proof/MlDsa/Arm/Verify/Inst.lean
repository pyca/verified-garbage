import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Inst
import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.Arm.KeyGenCT
import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Call`. -/
section

/-!
# ML-DSA on 32-bit ARM: calling the primitives only verification uses

As `ip_ok` and `ip_tr` (`KeyGen/Call.lean`), in the buffers of a `Site`:
`vg_mldsa_hint_bit_unpack`, `vg_mldsa_bit_unpack` and
`vg_mldsa_sample_in_ball` (whose fifth argument is on the stack),
`vg_mldsa_norm_lt`, `vg_mldsa_use_hint` and `vg_mldsa_unpack_t1`.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen (Ptr Arg callAt callAtS)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {y h : Ptr} {len om hl : Nat}

abbrev hbuArgs (y : Ptr) (len om : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr y), (.r1, .imm len), (.r2, .imm om), (.r3, .ptr h)]
abbrev hbuAll (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : List (Reg × Arg) :=
  VG.Proof.MlDsa.Arm.KeyGen.hbuArgs y len om h ++ [(.r12, .imm hl)]
abbrev hbuRd (L : Lay) (y : Ptr) (len : Nat) : List Region := [L.R (ix y.1) y.2 len]
abbrev hbuWr (L : Lay) (h : Ptr) (hl : Nat) : List Region := [L.R (ix h.1) h.2 (hl * 4)]

/-- The facts `vg_mldsa_hint_bit_unpack` needs of its arguments. -/
structure HbuOk (L : Lay) (Wb : List Nat) (y : Ptr) (len om : Nat) (h : Ptr) (hl : Nat) : Prop where
  py : PtrIn L y len
  ph : PtrIn L h (hl * 4)
  wh : ix h.1 ∈ Wb
  d1 : sepB L.sizes (tri y len) (tri h (hl * 4)) = true
  hp : (om, len - om) ∈ hintParams
  ho : om ≤ len
  hh : hl = 256 * (len - om)
  lt : 0 < len ∧ len < 2 ^ 32 ∧ om < 2 ^ 32 ∧ 0 < hl * 4 ∧ hl < 2 ^ 32

theorem HbuOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl) = true := by
  simp [glueOk, m.py.1, m.ph.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem hbuAll_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem hbuG {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) rd wr).gpr .r0 = L.ptr (ix y.1) + BitVec.ofNat 32 y.2 ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) rd wr).gpr .r2 = BitVec.ofNat 32 om ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) rd wr).gpr .r3 = L.ptr (ix h.1) + BitVec.ofNat 32 h.2 ∧
    stackArg (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) rd wr) 0 = BitVec.ofNat 32 hl :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.hbuAll_nodup (by simp) m.py.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.hbuAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.hbuAll_nodup (a := .imm om) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.hbuAll_nodup (by simp) m.ph.1],
    by rw [push_arg, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.hbuAll_nodup (a := .imm hl) (by simp)]; rfl⟩

theorem hbu_cov {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.py) covers_nil') (Covers.right (covers_cons' (hs.cwE m.ph m.wh) covers_nil')),
    covers_cons' (hs.cwE m.ph m.wh) covers_nil'⟩

theorem hbu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) :
    (hintBitUnpackContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl))) (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl)) := by
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl)
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.hbuG hs m (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl)
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have h4 := sp4 hs
  refine hbu_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.py l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, imm_toNat lh, hs.regE m.ph h0])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.py l0) (by rw [imm_toNat lh]; exact hs.fitE m.ph h0)
    (by rw [imm_toNat lo, imm_toNat ll]; exact m.hp) (by rw [imm_toNat lo, imm_toNat ll]; exact m.ho)
    (by rw [imm_toNat lo, imm_toNat ll, imm_toNat lh]; exact m.hh)
  · rw [imm_toNat ll, imm_toNat lh, hs.regE m.py l0, hs.regE m.ph h0]; exact hs.dE m.d1 (.inr m.wh)
  · rw [imm_toNat lh, hs.regE m.ph h0]; exact push_aE hs _ e1 _ _ m.ph
  · rw [imm_toNat ll, hs.regE m.py l0]; exact push_kE hs _ e1 _ _ m.py hstk
  · rw [imm_toNat lh, hs.regE m.ph h0]; exact push_kE hs _ e1 _ _ m.ph hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem hbu_okS {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri h (hl * 4), (1, 0, STK)]) s s' →
      (match VG.Spec.MlDsa.hintBitUnpack om (len - om) (bytesAt s.mem (lpa L y) len) with
        | some hint => s'.gpr .r0 = 1 ∧ HintIs s'.mem (lpa L h) (len - om) hint
        | none => s'.gpr .r0 = 0) → Q s') :
    WP isa (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.hbuArgs y len om h) (.imm hl)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hs m
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl)
  have hm := glueSt_mem s (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl)
  refine callVS hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.hbu_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [tri h (hl * 4)] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, hr₃, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, -⟩ := VG.Proof.MlDsa.Arm.KeyGen.hbuG hs m (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl)
  have := hbu_post hp
  have hb := push_bytesAt hs e1 hm (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl) m.py (by omega)
  rw [g0, g1, g2, g3, hs.addrE m.py l0, hs.addrE m.ph h0, imm_toNat ll, imm_toNat lo, hb] at this
  simp only [State.withRegions_mem, State.withRegions_gpr, hm₃, hr₃ .r0 (by decide)] at this
  exact this

theorem hbu_tr {c : Prog isa} (hc : Callee c (fun stk => hintBitUnpackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.HbuOk L Wb y len om h hl) {P : State → State → Prop}
    (hP : ∀ x y', P x y' → Site L Wb STK x ∧ Site L Wb STK y' ∧ x.sp = y'.sp ∧
      bytesAt x.mem (lpa L y) len = bytesAt y'.mem (lpa L y) len) :
    RelCT isa P (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.hbuArgs y len om h) (.imm hl)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lo, h0, lh⟩ := m.lt
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y' hxy => ?_
  obtain ⟨hx, hy, hsp, hl'⟩ := hP x y' hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := VG.Proof.MlDsa.Arm.KeyGen.hbuG hx m (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := VG.Proof.MlDsa.Arm.KeyGen.hbuG hy m (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl)
  have ex : VG.Proof.MlDsa.Arm.KeyGen.argR y' = VG.Proof.MlDsa.Arm.KeyGen.argR x := by simp only [VG.Proof.MlDsa.Arm.KeyGen.argR, hsp]
  have bx := push_bytesAt hx (glueSt_sp x (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl)) (glueSt_mem x _) (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x])
    (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl) m.py (by omega)
  have by' := push_bytesAt hy (glueSt_sp y' (VG.Proof.MlDsa.Arm.KeyGen.hbuAll y len om h hl)) (glueSt_mem y' _) (VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x])
    (VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl) m.py (by omega)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.hbuRd L y len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x], VG.Proof.MlDsa.Arm.KeyGen.hbuWr L h hl, VG.Proof.MlDsa.Arm.KeyGen.hbu_preS hx (by omega) m, ?_,
    hbu_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]) ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact VG.Proof.MlDsa.Arm.KeyGen.hbu_preS hy (by omega) m
  · rw [gx0, gy0, gx1, gy1, hx.addrE m.py l0, imm_toNat ll]
    exact bx.trans (hl'.trans by'.symm)
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hx m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hy m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.hbu_cov hy m).2).2

end

/-! ## `vg_mldsa_bit_unpack` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr} {len a b : Nat}

abbrev buArgs (v : Ptr) (len a b : Nat) : List (Reg × Arg) :=
  [(.r0, .ptr v), (.r1, .imm len), (.r2, .imm a), (.r3, .imm b)]
abbrev buAll (v : Ptr) (len a b : Nat) (f : Ptr) : List (Reg × Arg) := VG.Proof.MlDsa.Arm.KeyGen.buArgs v len a b ++ [(.r12, .ptr f)]
abbrev buRd (L : Lay) (v : Ptr) (len : Nat) : List Region := [L.R (ix v.1) v.2 len]
abbrev buWr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_bit_unpack` needs of its arguments. -/
structure BuOk (L : Lay) (Wb : List Nat) (v : Ptr) (len a b : Nat) (f : Ptr) : Prop where
  pv : PtrIn L v len
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v len) (tri f 1024) = true
  hab : (a, b) ∈ bitPackParams
  hl : len = 32 * bitlen (a + b)
  lt : 0 < len ∧ len < 2 ^ 32 ∧ a < 2 ^ 32 ∧ b < 2 ^ 32

theorem BuOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f) = true := by
  simp [glueOk, m.pv.1, m.pf.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem buAll_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem buG {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) rd wr).gpr .r0 = L.ptr (ix v.1) + BitVec.ofNat 32 v.2 ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) rd wr).gpr .r2 = BitVec.ofNat 32 a ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) rd wr).gpr .r3 = BitVec.ofNat 32 b ∧
    stackArg (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) rd wr) 0 =
      L.ptr (ix f.1) + BitVec.ofNat 32 f.2 :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.buAll_nodup (by simp) m.pv.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.buAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.buAll_nodup (a := .imm a) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.buAll_nodup (a := .imm b) (by simp)]; rfl,
    by rw [push_arg, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.buAll_nodup (by simp) m.pf.1]⟩

theorem bu_cov {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ VG.Proof.MlDsa.Arm.KeyGen.buWr L f) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.buWr L f) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pv) covers_nil') (Covers.right (covers_cons' (hs.cwE m.pf m.wf) covers_nil')),
    covers_cons' (hs.cwE m.pf m.wf) covers_nil'⟩

theorem bu_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) :
    (bitUnpackContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f))) (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f)) := by
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f)
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.buG hs m (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f)
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  have h4 := sp4 hs
  refine bu_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.pv l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, hs.regE m.pf (by decide)])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.pv l0) (hs.fitE m.pf (by decide))
    (by rw [imm_toNat la, imm_toNat lb]; exact m.hab) (by rw [imm_toNat la, imm_toNat lb, imm_toNat ll]; exact m.hl)
  · rw [imm_toNat ll, hs.regE m.pv l0, hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inr m.wf)
  · rw [hs.regE m.pf (by decide)]; exact push_aE hs _ e1 _ _ m.pf
  · rw [imm_toNat ll, hs.regE m.pv l0]; exact push_kE hs _ e1 _ _ m.pv hstk
  · rw [hs.regE m.pf (by decide)]; exact push_kE hs _ e1 _ _ m.pf hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem bu_okS {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (lpa L v) len) a b)) → Q s') :
    WP isa (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.buArgs v len a b) (.ptr f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.bu_cov hs m
  obtain ⟨l0, ll, la, lb⟩ := m.lt
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f)
  have hm := glueSt_mem s (VG.Proof.MlDsa.Arm.KeyGen.buAll v len a b f)
  refine callVS hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.bu_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 =>
      hQ s' (hs.keptW [tri f 1024] (by have := hc.stack; omega) hk) ?_
  obtain ⟨s₃, hm₃, -, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.buG hs m (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f)
  have := bu_post hp
  have hb := push_bytesAt hs e1 hm (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f) m.pv (by omega)
  rw [g0, g1, g2, g3, ga, hs.addrE m.pv l0, hs.addrE m.pf (by decide), imm_toNat ll, imm_toNat la, imm_toNat lb,
    hb] at this
  simp only [State.withRegions_mem, hm₃] at this
  exact this

theorem bu_tr {c : Prog isa} (hc : Callee c (fun stk => bitUnpackContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BuOk L Wb v len a b f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAtS name c (VG.Proof.MlDsa.Arm.KeyGen.buArgs v len a b) (.ptr f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := VG.Proof.MlDsa.Arm.KeyGen.buG hx m (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := VG.Proof.MlDsa.Arm.KeyGen.buG hy m (VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.buWr L f)
  have ex : VG.Proof.MlDsa.Arm.KeyGen.argR y = VG.Proof.MlDsa.Arm.KeyGen.argR x := by simp only [VG.Proof.MlDsa.Arm.KeyGen.argR, hsp]
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.buRd L v len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x], VG.Proof.MlDsa.Arm.KeyGen.buWr L f, VG.Proof.MlDsa.Arm.KeyGen.bu_preS hx (by omega) m, ?_,
    bu_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]),
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact VG.Proof.MlDsa.Arm.KeyGen.bu_preS hy (by omega) m
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hx m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hy m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.bu_cov hy m).2).2

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {ct c w : Ptr} {len tau : Nat}

abbrev ballArgs (ct : Ptr) (len tau : Nat) (c : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr ct), (.r1, .imm len), (.r2, .imm tau), (.r3, .ptr c)]
abbrev ballAll (ct : Ptr) (len tau : Nat) (c w : Ptr) : List (Reg × Arg) := VG.Proof.MlDsa.Arm.KeyGen.ballArgs ct len tau c ++ [(.r12, .ptr w)]
abbrev ballRd (L : Lay) (ct : Ptr) (len : Nat) : List Region := [L.R (ix ct.1) ct.2 len]
abbrev ballWr (L : Lay) (c w : Ptr) : List Region := [L.R (ix c.1) c.2 1024, L.R (ix w.1) w.2 2048]

/-- The facts `vg_mldsa_sample_in_ball` needs of its arguments. -/
structure BallOk (L : Lay) (Wb : List Nat) (ct : Ptr) (len tau : Nat) (c w : Ptr) : Prop where
  pct : PtrIn L ct len
  pc : PtrIn L c 1024
  pw : PtrIn L w 2048
  wc : ix c.1 ∈ Wb
  ww : ix w.1 ∈ Wb
  d1 : sepB L.sizes (tri ct len) (tri c 1024) = true
  d2 : sepB L.sizes (tri ct len) (tri w 2048) = true
  d3 : sepB L.sizes (tri c 1024) (tri w 2048) = true
  hp : (len, tau) ∈ ballParams
  lt : 0 < len ∧ len < 2 ^ 32 ∧ tau < 2 ^ 32

theorem BallOk.hg (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w) = true := by
  simp [glueOk, m.pct.1, m.pc.1, m.pw.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem ballAll_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]; decide

theorem ballG {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) (rd wr : List Region) :
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) rd wr).gpr .r0 = L.ptr (ix ct.1) + BitVec.ofNat 32 ct.2 ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) rd wr).gpr .r1 = BitVec.ofNat 32 len ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) rd wr).gpr .r2 = BitVec.ofNat 32 tau ∧
    (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) rd wr).gpr .r3 = L.ptr (ix c.1) + BitVec.ofNat 32 c.2 ∧
    stackArg (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) rd wr) 0 =
      L.ptr (ix w.1) + BitVec.ofNat 32 w.2 :=
  ⟨by rw [view_r0, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.ballAll_nodup (by simp) m.pct.1],
    by rw [view_r1, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.ballAll_nodup (a := .imm len) (by simp)]; rfl,
    by rw [view_r2, pushed_gpr, glueSt_arg s m.hg VG.Proof.MlDsa.Arm.KeyGen.ballAll_nodup (a := .imm tau) (by simp)]; rfl,
    by rw [view_r3, pushed_gpr, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.ballAll_nodup (by simp) m.pc.1],
    by rw [push_arg, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.ballAll_nodup (by simp) m.pw.1]⟩

theorem ball_cov {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.pct) covers_nil')
    (Covers.right (covers_cons' (hs.cwE m.pc m.wc) (covers_cons' (hs.cwE m.pw m.ww) covers_nil'))),
    covers_cons' (hs.cwE m.pc m.wc) (covers_cons' (hs.cwE m.pw m.ww) covers_nil')⟩

theorem ball_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : 4 + stk ≤ STK)
    (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) :
    (sampleInBallContract Arm.abi stk).pre
      (view (pushed [.r12] (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w))) (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w)) := by
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w)
  obtain ⟨g0, g1, g2, g3, ga⟩ := VG.Proof.MlDsa.Arm.KeyGen.ballG hs m (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w)
  obtain ⟨l0, ll, lt⟩ := m.lt
  have h4 := sp4 hs
  refine ball_pre g0 g1 g2 g3 ga
    (by rw [State.withRegions_rd, imm_toNat ll, hs.regE m.pct l0, push_argAddr _ e1]; rfl)
    (by rw [State.withRegions_wr, hs.regE m.pc (by decide), hs.regE m.pw (by decide)])
    (by rw [push_spN _ e1 _ _ h4]; have := hs.spk; omega) (push_fit _ _ _ h4 e1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [imm_toNat ll]; exact hs.fitE m.pct l0) (hs.fitE m.pc (by decide))
    (hs.fitE m.pw (by decide)) (by rw [imm_toNat ll, imm_toNat lt]; exact m.hp)
  · rw [imm_toNat ll, hs.regE m.pct l0, hs.regE m.pc (by decide)]; exact hs.dE m.d1 (.inr m.wc)
  · rw [imm_toNat ll, hs.regE m.pct l0, hs.regE m.pw (by decide)]; exact hs.dE m.d2 (.inr m.ww)
  · rw [hs.regE m.pc (by decide), hs.regE m.pw (by decide)]; exact hs.dE m.d3 (.inl m.wc)
  · rw [hs.regE m.pc (by decide)]; exact push_aE hs _ e1 _ _ m.pc
  · rw [hs.regE m.pw (by decide)]; exact push_aE hs _ e1 _ _ m.pw
  · rw [imm_toNat ll, hs.regE m.pct l0]; exact push_kE hs _ e1 _ _ m.pct hstk
  · rw [hs.regE m.pc (by decide)]; exact push_kE hs _ e1 _ _ m.pc hstk
  · rw [hs.regE m.pw (by decide)]; exact push_kE hs _ e1 _ _ m.pw hstk
  · exact push_kA hs _ e1 _ _ hstk

theorem ball_okS {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : 4 + S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri c 1024, tri w 2048, (1, 0, STK)]) s s' →
      (s'.gpr .r0 = 1 → Reduced s'.mem (lpa L c)) →
      Outcome (fun b => (VG.Spec.MlDsa.sampleInBall tau b.ball (bytesAt s.mem (lpa L ct) len)).map toRq) (s'.gpr .r0)
        (polyAt s'.mem (lpa L c)) → Q s') :
    WP isa (callAtS name cd (VG.Proof.MlDsa.Arm.KeyGen.ballArgs ct len tau c) (.ptr w)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.ball_cov hs m
  obtain ⟨l0, ll, lt⟩ := m.lt
  have e1 := glueSt_sp s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w)
  have hm := glueSt_mem s (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w)
  refine callVS hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.ball_preS hs (by omega) m) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk h3 => ?_
  obtain ⟨s₃, hm₃, hr₃, hp⟩ := h3
  obtain ⟨g0, g1, g2, g3, -⟩ := VG.Proof.MlDsa.Arm.KeyGen.ballG hs m (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w)
  have := ball_post hp
  have hb := push_bytesAt hs e1 hm (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR s]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w) m.pct (by omega)
  rw [g0, g1, g2, g3, hs.addrE m.pct l0, hs.addrE m.pc (by decide), imm_toNat ll, imm_toNat lt, hb] at this
  simp only [State.withRegions_mem, State.withRegions_gpr, hm₃, hr₃ .r0 (by decide)] at this
  exact hQ s' (hs.keptW [tri c 1024, tri w 2048] (by have := hc.stack; omega) hk) this.1 this.2

theorem ball_tr {cd : Prog isa} (hc : Callee cd (fun stk => sampleInBallContract Arm.abi stk) S) (hS : 4 + S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.BallOk L Wb ct len tau c w) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧
      bytesAt x.mem (lpa L ct) len = bytesAt y.mem (lpa L ct) len) :
    RelCT isa P (callAtS name cd (VG.Proof.MlDsa.Arm.KeyGen.ballArgs ct len tau c) (.ptr w)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨l0, ll, lt⟩ := m.lt
  refine callVS_tr hver.1 hver.2.1 m.hg (fun x y h => (hP x y h).2.2.1)
    (fun x y h => ⟨sp4 (hP x y h).1, sp4 (hP x y h).2.1⟩) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, hl'⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3, gxa⟩ := VG.Proof.MlDsa.Arm.KeyGen.ballG hx m (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w)
  obtain ⟨gy0, gy1, gy2, gy3, gya⟩ := VG.Proof.MlDsa.Arm.KeyGen.ballG hy m (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x]) (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w)
  have ex : VG.Proof.MlDsa.Arm.KeyGen.argR y = VG.Proof.MlDsa.Arm.KeyGen.argR x := by simp only [VG.Proof.MlDsa.Arm.KeyGen.argR, hsp]
  have bx := push_bytesAt hx (glueSt_sp x (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w)) (glueSt_mem x _) (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x])
    (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w) m.pct (by omega)
  have by' := push_bytesAt hy (glueSt_sp y (VG.Proof.MlDsa.Arm.KeyGen.ballAll ct len tau c w)) (glueSt_mem y _) (VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x])
    (VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w) m.pct (by omega)
  refine ⟨VG.Proof.MlDsa.Arm.KeyGen.ballRd L ct len ++ [VG.Proof.MlDsa.Arm.KeyGen.argR x], VG.Proof.MlDsa.Arm.KeyGen.ballWr L c w, VG.Proof.MlDsa.Arm.KeyGen.ball_preS hx (by omega) m, ?_,
    ball_pub (by simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, glueSt_sp, hsp])
      (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2]) (by rw [gx3, gy3]) (by rw [gxa, gya]) ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← ex]; exact VG.Proof.MlDsa.Arm.KeyGen.ball_preS hy (by omega) m
  · rw [gx0, gy0, gx1, gy1, hx.addrE m.pct l0, imm_toNat ll]
    exact bx.trans (hl'.trans by'.symm)
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hx m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hx m).1 (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hx m).2).2
  · rw [← ex]; exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hy m).2).1
  · exact (push_cov _ (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hy m).1 (VG.Proof.MlDsa.Arm.KeyGen.ball_cov hy m).2).2

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {f : Ptr} {bd : Nat}

abbrev nlArgs (f : Ptr) (bd : Nat) : List (Reg × Arg) := [(.r0, .ptr f), (.r1, .imm bd)]

theorem nl_hg (pf : PtrIn L f 1024) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd) = true := by
  simp [glueOk, pf.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem nlArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem nl_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (pf : PtrIn L f 1024)
    (hr : Reduced s.mem (lpa L f)) :
    (normLtContract Arm.abi stk).pre (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd)) [L.R (ix f.1) f.2 1024] []) := by
  have hsp := view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd) [L.R (ix f.1) f.2 1024] []
  refine normLt_pre (by rw [view_r0, hs.gE (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (by simp) pf.1])
    (by rw [State.withRegions_rd, hs.regE pf (by decide)]) rfl (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    (by rw [hs.regE pf (by decide)]; exact hs.kE pf hstk hsp) (hs.fitE pf (by decide)) ?_
  rw [view_glue_mem, hs.addrE pf (by decide)]; exact hr

theorem nl_ok {c : Prog isa} (hc : Callee c (fun stk => normLtContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (pf : PtrIn L f 1024) (hbd : bd < 2 ^ 32)
    (hr : Reduced s.mem (lpa L f)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [(1, 0, STK)]) s s' →
      s'.gpr .r0 = (if normRq [polyAt s.mem (lpa L f)] < bd then 1 else 0) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV hver.1 (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) (VG.Proof.MlDsa.Arm.KeyGen.nl_preS hs (Nat.le_trans hstk hS) pf hr)
    (Covers.append_left (covers_cons' (hs.crE pf) covers_nil') covers_nil') covers_nil'
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [] (Nat.le_trans hc.stack hS) hk) ?_
  have := normLt_post hp
  rw [State.withRegions_gpr, view_r0, view_r1, hs.gE (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (by simp) pf.1,
    glueSt_arg s (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (a := .imm bd) (by simp), view_glue_mem, hs.addrE pf (by decide)] at this
  simp only [argVal, imm_toNat hbd] at this
  exact this

theorem nl_tr {c : Prog isa} (hc : Callee c (fun stk => normLtContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (pf : PtrIn L f 1024) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L f) ∧
      Reduced y.mem (lpa L f)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.nlArgs f bd)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  refine ⟨[L.R (ix f.1) f.2 1024], [], VG.Proof.MlDsa.Arm.KeyGen.nl_preS hx (Nat.le_trans hstk hS) pf rx,
    VG.Proof.MlDsa.Arm.KeyGen.nl_preS hy (Nat.le_trans hstk hS) pf ry, normLt_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [view_r0, view_r0, hx.gE (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (by simp) pf.1,
        hy.gE (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (by simp) pf.1])
      (by rw [view_r1, view_r1]; exact hx.gpr_eq hy (VG.Proof.MlDsa.Arm.KeyGen.nl_hg pf) VG.Proof.MlDsa.Arm.KeyGen.nlArgs_nodup (a := .imm bd) (by simp)),
    Covers.append_left (covers_cons' (hx.crE pf) covers_nil') covers_nil', covers_nil',
    Covers.append_left (covers_cons' (hy.crE pf) covers_nil') covers_nil', covers_nil'⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {h r o : Ptr} {g2 : Nat}

abbrev uhArgs (h r : Ptr) (g2 : Nat) (o : Ptr) : List (Reg × Arg) :=
  [(.r0, .ptr h), (.r1, .ptr r), (.r2, .imm g2), (.r3, .ptr o)]
abbrev uhRd (L : Lay) (h r : Ptr) : List Region := [L.R (ix h.1) h.2 1024, L.R (ix r.1) r.2 1024]
abbrev uhWr (L : Lay) (o : Ptr) : List Region := [L.R (ix o.1) o.2 1024]

/-- The facts `vg_mldsa_use_hint` needs of its arguments. -/
structure UhOk (L : Lay) (Wb : List Nat) (h r : Ptr) (g2 : Nat) (o : Ptr) : Prop where
  ph : PtrIn L h 1024
  pr : PtrIn L r 1024
  po : PtrIn L o 1024
  wo : ix o.1 ∈ Wb
  d1 : sepB L.sizes (tri h 1024) (tri o 1024) = true
  d2 : sepB L.sizes (tri r 1024) (tri o 1024) = true
  hg : g2 ∈ gamma2s
  lt : g2 < 2 ^ 32

theorem UhOk.hg' (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o) = true := by
  simp [glueOk, m.ph.1, m.pr.1, m.po.1, show ∀ v, argOk (.imm v) = true from fun _ => rfl]

theorem uhArgs_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem uhG {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o) (rd wr : List Region) :
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) rd wr).gpr .r0 = L.ptr (ix h.1) + BitVec.ofNat 32 h.2 ∧
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) rd wr).gpr .r1 = L.ptr (ix r.1) + BitVec.ofNat 32 r.2 ∧
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) rd wr).gpr .r2 = BitVec.ofNat 32 g2 ∧
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) rd wr).gpr .r3 = L.ptr (ix o.1) + BitVec.ofNat 32 o.2 :=
  ⟨by rw [view_r0, hs.gE m.hg' VG.Proof.MlDsa.Arm.KeyGen.uhArgs_nodup (by simp) m.ph.1],
    by rw [view_r1, hs.gE m.hg' VG.Proof.MlDsa.Arm.KeyGen.uhArgs_nodup (by simp) m.pr.1],
    by rw [view_r2, glueSt_arg s m.hg' VG.Proof.MlDsa.Arm.KeyGen.uhArgs_nodup (a := .imm g2) (by simp)]; rfl,
    by rw [view_r3, hs.gE m.hg' VG.Proof.MlDsa.Arm.KeyGen.uhArgs_nodup (by simp) m.po.1]⟩

theorem uh_cov {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o) :
    Covers (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r ++ VG.Proof.MlDsa.Arm.KeyGen.uhWr L o) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o) s.wr :=
  ⟨Covers.append_left (covers_cons' (hs.crE m.ph) (covers_cons' (hs.crE m.pr) covers_nil'))
    (Covers.right (covers_cons' (hs.cwE m.po m.wo) covers_nil')), covers_cons' (hs.cwE m.po m.wo) covers_nil'⟩

theorem uh_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) :
    (useHintContract Arm.abi stk).pre (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)) := by
  have hsp := view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o) (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)
  obtain ⟨g0, g1, gg, g3⟩ := VG.Proof.MlDsa.Arm.KeyGen.uhG hs m (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)
  refine useHint_pre g0 g1 gg g3 (by rw [State.withRegions_rd, hs.regE m.ph (by decide), hs.regE m.pr (by decide)])
    (by rw [State.withRegions_wr, hs.regE m.po (by decide)]) (by rw [hsp]; exact Nat.le_trans hstk hs.spk)
    ?_ ?_ ?_ ?_ ?_ (hs.fitE m.ph (by decide)) (hs.fitE m.pr (by decide)) (hs.fitE m.po (by decide))
    (by rw [imm_toNat m.lt]; exact m.hg) ?_
  · rw [hs.regE m.ph (by decide), hs.regE m.po (by decide)]; exact hs.dE m.d1 (.inr m.wo)
  · rw [hs.regE m.pr (by decide), hs.regE m.po (by decide)]; exact hs.dE m.d2 (.inr m.wo)
  · rw [hs.regE m.ph (by decide)]; exact hs.kE m.ph hstk hsp
  · rw [hs.regE m.pr (by decide)]; exact hs.kE m.pr hstk hsp
  · rw [hs.regE m.po (by decide)]; exact hs.kE m.po hstk hsp
  · rw [view_glue_mem, hs.addrE m.pr (by decide)]; exact hr

theorem uh_ok {c : Prog isa} (hc : Callee c (fun stk => useHintContract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o)
    (hr : Reduced s.mem (lpa L r)) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri o 1024, (1, 0, STK)]) s s' →
      NatPolyIs s'.mem (lpa L o) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint g2 hj rj).toNat)
        ((hintAt s.mem (lpa L h) 1).headD (Vector.replicate n false)) (polyAt s.mem (lpa L r))) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  obtain ⟨c1, c2⟩ := VG.Proof.MlDsa.Arm.KeyGen.uh_cov hs m
  refine callV hver.1 m.hg' (VG.Proof.MlDsa.Arm.KeyGen.uh_preS hs (Nat.le_trans hstk hS) m hr) c1 c2
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri o 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1, gg, g3⟩ := VG.Proof.MlDsa.Arm.KeyGen.uhG hs m (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)
  have := useHint_post hp
  rwa [State.withRegions_mem, g0, g1, gg, g3, hs.addrE m.ph (by decide), hs.addrE m.pr (by decide),
    hs.addrE m.po (by decide), view_glue_mem, imm_toNat m.lt] at this

theorem uh_tr {c : Prog isa} (hc : Callee c (fun stk => useHintContract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.UhOk L Wb h r g2 o) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp ∧ Reduced x.mem (lpa L r) ∧
      Reduced y.mem (lpa L r)) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.uhArgs h r g2 o)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg' fun x y hxy => ?_
  obtain ⟨hx, hy, hsp, rx, ry⟩ := hP x y hxy
  obtain ⟨gx0, gx1, gx2, gx3⟩ := VG.Proof.MlDsa.Arm.KeyGen.uhG hx m (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)
  obtain ⟨gy0, gy1, gy2, gy3⟩ := VG.Proof.MlDsa.Arm.KeyGen.uhG hy m (VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r) (VG.Proof.MlDsa.Arm.KeyGen.uhWr L o)
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.uhRd L h r, VG.Proof.MlDsa.Arm.KeyGen.uhWr L o, VG.Proof.MlDsa.Arm.KeyGen.uh_preS hx (Nat.le_trans hstk hS) m rx, VG.Proof.MlDsa.Arm.KeyGen.uh_preS hy (Nat.le_trans hstk hS) m ry,
    useHint_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [gx0, gy0]) (by rw [gx1, gy1]) (by rw [gx2, gy2])
      (by rw [gx3, gy3]), (VG.Proof.MlDsa.Arm.KeyGen.uh_cov hx m).1, (VG.Proof.MlDsa.Arm.KeyGen.uh_cov hx m).2, (VG.Proof.MlDsa.Arm.KeyGen.uh_cov hy m).1, (VG.Proof.MlDsa.Arm.KeyGen.uh_cov hy m).2⟩

end

/-! ## `vg_mldsa_unpack_t1` -/

section
variable {L : Lay} {Wb : List Nat} {STK S : Nat} {v f : Ptr}

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.r0, .ptr v), (.r1, .ptr f)]
abbrev t1Rd (L : Lay) (v : Ptr) : List Region := [L.R (ix v.1) v.2 320]
abbrev t1Wr (L : Lay) (f : Ptr) : List Region := [L.R (ix f.1) f.2 1024]

/-- The facts `vg_mldsa_unpack_t1` needs of its arguments. -/
structure T1Ok (L : Lay) (Wb : List Nat) (v f : Ptr) : Prop where
  pv : PtrIn L v 320
  pf : PtrIn L f 1024
  wf : ix f.1 ∈ Wb
  d1 : sepB L.sizes (tri v 320) (tri f 1024) = true

theorem T1Ok.hg (m : VG.Proof.MlDsa.Arm.KeyGen.T1Ok L Wb v f) : glueOk (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f) = true := by
  simp [glueOk, m.pv.1, m.pf.1]

theorem t1Args_nodup : ((VG.Proof.MlDsa.Arm.KeyGen.t1Args v f).map Prod.fst).Nodup := by
  simp only [List.map_cons, List.map_nil]; decide

theorem t1G {s : State} (hs : Site L Wb STK s) (m : VG.Proof.MlDsa.Arm.KeyGen.T1Ok L Wb v f) (rd wr : List Region) :
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f)) rd wr).gpr .r0 = L.ptr (ix v.1) + BitVec.ofNat 32 v.2 ∧
    (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f)) rd wr).gpr .r1 = L.ptr (ix f.1) + BitVec.ofNat 32 f.2 :=
  ⟨by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pv.1], by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pf.1]⟩

theorem t1_preS {s : State} (hs : Site L Wb STK s) {stk : Nat} (hstk : stk ≤ STK) (m : VG.Proof.MlDsa.Arm.KeyGen.T1Ok L Wb v f) :
    (unpackT1Contract Arm.abi stk).pre (view (glueSt s (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f)) (VG.Proof.MlDsa.Arm.KeyGen.t1Rd L v) (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f)) := by
  have hsp := view_glue_sp s (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f) (VG.Proof.MlDsa.Arm.KeyGen.t1Rd L v) (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f)
  refine t1_pre (by rw [view_r0, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pv.1])
    (by rw [view_r1, hs.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pf.1])
    (by rw [State.withRegions_rd, hs.regE m.pv (by decide)]) (by rw [State.withRegions_wr, hs.regE m.pf (by decide)])
    (by rw [hsp]; exact Nat.le_trans hstk hs.spk) ?_ ?_ ?_ (hs.fitE m.pv (by decide)) (hs.fitE m.pf (by decide))
  · rw [hs.regE m.pv (by decide), hs.regE m.pf (by decide)]; exact hs.dE m.d1 (.inr m.wf)
  · rw [hs.regE m.pv (by decide)]; exact hs.kE m.pv hstk hsp
  · rw [hs.regE m.pf (by decide)]; exact hs.kE m.pf hstk hsp

theorem t1_ok {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract Arm.abi stk) S) {s : State}
    (hs : Site L Wb STK s) (hS : S ≤ STK) {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.T1Ok L Wb v f) {Q : State → Prop}
    (hQ : ∀ s', Kept (L.RL [tri f 1024, (1, 0, STK)]) s s' →
      PolyIs s'.mem (lpa L f) ((simpleBitUnpack (bytesAt s.mem (lpa L v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) → Q s') :
    WP isa (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f)) s Q := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  have cw : Covers (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f) s.wr := covers_cons' (hs.cwE m.pf m.wf) covers_nil'
  refine callV hver.1 m.hg (VG.Proof.MlDsa.Arm.KeyGen.t1_preS hs (Nat.le_trans hstk hS) m)
    (Covers.append_left (covers_cons' (hs.crE m.pv) covers_nil') (Covers.right cw)) cw
    (by have := hs.spk; have := hc.stack; omega) fun s' hk hp =>
      hQ s' (hs.keptW [tri f 1024] (Nat.le_trans hc.stack hS) hk) ?_
  obtain ⟨g0, g1⟩ := VG.Proof.MlDsa.Arm.KeyGen.t1G hs m (VG.Proof.MlDsa.Arm.KeyGen.t1Rd L v) (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f)
  have := t1_post hp
  rwa [State.withRegions_mem, g0, g1, hs.addrE m.pv (by decide), hs.addrE m.pf (by decide),
    view_glue_mem] at this

theorem t1_tr {c : Prog isa} (hc : Callee c (fun stk => unpackT1Contract Arm.abi stk) S) (hS : S ≤ STK)
    {name : String} (m : VG.Proof.MlDsa.Arm.KeyGen.T1Ok L Wb v f) {P : State → State → Prop}
    (hP : ∀ x y, P x y → Site L Wb STK x ∧ Site L Wb STK y ∧ x.sp = y.sp) :
    RelCT isa P (callAt name c (VG.Proof.MlDsa.Arm.KeyGen.t1Args v f)) fun _ _ => True := by
  obtain ⟨stk, hstk, hver⟩ := hc.verified
  refine callV_tr hver.1 hver.2.1 m.hg fun x y hxy => ?_
  obtain ⟨hx, hy, hsp⟩ := hP x y hxy
  have cx : Covers (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f) x.wr := covers_cons' (hx.cwE m.pf m.wf) covers_nil'
  have cy : Covers (VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f) y.wr := covers_cons' (hy.cwE m.pf m.wf) covers_nil'
  exact ⟨VG.Proof.MlDsa.Arm.KeyGen.t1Rd L v, VG.Proof.MlDsa.Arm.KeyGen.t1Wr L f, VG.Proof.MlDsa.Arm.KeyGen.t1_preS hx (Nat.le_trans hstk hS) m, VG.Proof.MlDsa.Arm.KeyGen.t1_preS hy (Nat.le_trans hstk hS) m,
    t1_pub (by rw [view_glue_sp, view_glue_sp, hsp])
      (by rw [view_r0, view_r0, hx.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pv.1, hy.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pv.1])
      (by rw [view_r1, view_r1, hx.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pf.1, hy.gE m.hg VG.Proof.MlDsa.Arm.KeyGen.t1Args_nodup (by simp) m.pf.1]),
    Covers.append_left (covers_cons' (hx.crE m.pv) covers_nil') (Covers.right cx), cx,
    Covers.append_left (covers_cons' (hy.crE m.pv) covers_nil') (Covers.right cy), cy⟩

end

end VG.Proof.MlDsa.Arm.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Lay`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: its parameters, precondition and buffers

The facts about the parameter sets the proof uses (`VFacts`); the precondition
of the shared contract, evaluated (`VPre`, `vpre_of`); and the buffers of the
function (`vlay`): `scratch`, the stack, `pk`, `mu` and `sig`, of which only
`scratch` (and the stack) are written, and the inputs, only read, may overlap
each other. `vsep` proves the facts about the offsets of pointers into them by
`omega`, for any parameter set.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = oHint p + (p.ω + p.k)
  hint : oHint p = p.ctildeLen + lenZ p * p.ℓ
  ct : (p.ctildeLen = 32 ∨ p.ctildeLen = 48 ∨ p.ctildeLen = 64)
  lz : (lenZ p = 576 ∨ lenZ p = 640)
  om : 55 ≤ p.ω ∧ p.ω ≤ 80
  w1 : p.k * w1Len p ≤ 1024 ∧ 0 < p.k * w1Len p ∧ encodable (BitVec.ofNat 32 (p.k * w1Len p)) = true
  w1l : w1Len p = 128 ∨ (w1Len p = 192 ∧ p.k ≤ 5)
  scr : 8192 + 1024 * (20 + 8 * p.k) ≤ scrLen p ∧ scrLen p < 2 ^ 32
  hp : (p.ω, p.k) ∈ Spec.MlDsa.hintParams
  bu : (p.γ₁ - 1, p.γ₁) ∈ Spec.MlDsa.bitPackParams ∧ lenZ p = 32 * Spec.MlDsa.bitlen (p.γ₁ - 1 + p.γ₁) ∧
    p.γ₁ < 2 ^ 32
  ball : (p.ctildeLen, p.τ) ∈ Spec.MlDsa.ballParams ∧ p.τ < 2 ^ 32
  g2 : p.γ₂ ∈ Spec.MlDsa.gamma2s ∧ p.γ₂ < 2 ^ 32
  sbp : w1Max p ∈ Spec.MlDsa.simpleBitPackBounds ∧ w1Len p = 32 * Spec.MlDsa.bitlen (w1Max p) ∧ w1Max p < 2 ^ 32
  nb : p.γ₁ - p.β < 2 ^ 32 ∧ 0 < p.γ₁ - p.β
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.Arm.Verify.VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The precondition -/

section
variable (σ : State)

abbrev vPk : BitVec 32 := σ.gpr .r0
abbrev vMu : BitVec 32 := σ.gpr .r1
abbrev vSg : BitVec 32 := σ.gpr .r2
abbrev vScr : BitVec 32 := σ.gpr .r3

end

/-- The precondition of `verifyContract` with `STK` bytes of stack. -/
structure VPre (p : Params) (STK : Nat) (σ : State) : Prop where
  stk : STK ≤ σ.sp.toNat
  rd : σ.rd = [regA (VG.Proof.MlDsa.Arm.Verify.vPk σ) p.pkLen, regA (VG.Proof.MlDsa.Arm.Verify.vMu σ) 64, regA (VG.Proof.MlDsa.Arm.Verify.vSg σ) p.sigLen]
  wr : σ.wr = [regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p)]
  d_pc : (regA (VG.Proof.MlDsa.Arm.Verify.vPk σ) p.pkLen).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p))
  d_mc : (regA (VG.Proof.MlDsa.Arm.Verify.vMu σ) 64).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p))
  d_sc : (regA (VG.Proof.MlDsa.Arm.Verify.vSg σ) p.sigLen).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p))
  b_p : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vPk σ) p.pkLen)
  b_m : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vMu σ) 64)
  b_s : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vSg σ) p.sigLen)
  b_c : (below σ STK).Disjoint (regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p))
  f_p : (VG.Proof.MlDsa.Arm.Verify.vPk σ).toNat + p.pkLen ≤ 2 ^ 32
  f_m : (VG.Proof.MlDsa.Arm.Verify.vMu σ).toNat + 64 ≤ 2 ^ 32
  f_s : (VG.Proof.MlDsa.Arm.Verify.vSg σ).toNat + p.sigLen ≤ 2 ^ 32
  f_c : (VG.Proof.MlDsa.Arm.Verify.vScr σ).toNat + scrLen p ≤ 2 ^ 32

theorem vpre_of {p : Params} {n : Nat} {σ : State} (h : (Spec.MlDsa.verifyContract p Arm.abi (n + 1)).pre σ) :
    VG.Proof.MlDsa.Arm.Verify.VPre p (n + 1) σ := by
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-! ## The buffers -/

/-- `scratch` (0), the stack (1), `pk` (2), `mu` (3) and `sig` (4). -/
def vlay (p : Params) (STK : Nat) (σ : State) : Lay :=
  ⟨fun i => [VG.Proof.MlDsa.Arm.Verify.vScr σ, σ.sp - BitVec.ofNat 32 STK, VG.Proof.MlDsa.Arm.Verify.vPk σ, VG.Proof.MlDsa.Arm.Verify.vMu σ, VG.Proof.MlDsa.Arm.Verify.vSg σ].getD i 0,
    [scrLen p, STK, p.pkLen, 64, p.sigLen]⟩

theorem vlay_sizes (p : Params) (STK : Nat) (σ : State) :
    (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).sizes = [scrLen p, STK, p.pkLen, 64, p.sigLen] := rfl

/-- The buffers written: `scratch` and the stack. -/
abbrev vWb : List Nat := [0, 1]

theorem vlay_ok {p : Params} {STK : Nat} {σ : State} (hp : VG.Proof.MlDsa.Arm.Verify.VPre p STK σ) : OkW (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb := by
  have es : (⟨State.addr (σ.sp - BitVec.ofNat 32 STK), STK⟩ : Region) = below σ STK := by
    rw [VG.Proof.MlKem.Arm.addr_sub hp.stk]
  refine ⟨fun i hi => ?_, fun i hi j hj hij hw => ?_⟩
  · simp only [VG.Proof.MlDsa.Arm.Verify.vlay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hp.f_c
    · show (σ.sp - BitVec.ofNat 32 STK).toNat + STK ≤ 2 ^ 32
      have := hp.stk; have := σ.sp.isLt; bv_omega
    · exact hp.f_p
    · exact hp.f_m
    · exact hp.f_s
  · simp only [VG.Proof.MlDsa.Arm.Verify.vlay, List.length_cons, List.length_nil] at hi hj
    simp only [VG.Proof.MlDsa.Arm.Verify.vWb, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.MlDsa.Arm.Verify.vlay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_c.symm
    · exact hp.d_pc.symm
    · exact hp.d_mc.symm
    · exact hp.d_sc.symm
    · rw [es]; exact hp.b_c
    · rw [es]; exact hp.b_p
    · rw [es]; exact hp.b_m
    · rw [es]; exact hp.b_s
    · exact hp.d_pc
    · rw [es]; exact hp.b_p.symm
    · exact hp.d_mc
    · rw [es]; exact hp.b_m.symm
    · exact hp.d_sc
    · rw [es]; exact hp.b_s.symm

/-- Decides a fact about offsets in the buffers, for any parameter set with
the facts `hF`. -/
syntax "vsep " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vsep $hF) => `(tactic| vsep $hF [])
  | `(tactic| vsep $hF [$ls,*]) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).pk
      have := ($hF).sig; have := ($hF).hint; have := ($hF).ct; have := ($hF).lz; have := ($hF).om
      have := ($hF).w1; have := ($hF).w1l
      try dsimp only [$ls,*]
      try dsimp only [sepB, sepAll, VG.Proof.MlDsa.Arm.KeyGen.inB, tri, ix, sc, pS, pH, pZ, pC, pT, pT2, pW, pW1, pA, oP, oSS, oSB, oB, oCT]
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [sepB, sepAll, VG.Proof.MlDsa.Arm.KeyGen.inB, vlay_sizes, List.getD_cons_zero,
        List.getD_cons_succ, List.length_cons, List.length_nil, List.all_cons, List.all_nil, tri, ix,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.and_true, Bool.true_and,
        true_and, and_true, true_or, or_true, Nat.zero_add, oP, oSS, oSB, oB, oCT, sc, pS, pH, pZ, pC, pT, pT2,
        pW, pW1, pA, false_or, or_false, decide_eq_true_iff, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inv`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: what holds throughout, and the prologue

What holds of the state throughout (`VC`: the layout, the permissions and
stack pointer of the entry state, our caller's registers saved in `scratch`,
and the inputs), which a part keeps if it writes only `scratch` and the stack,
apart from the saved registers (`vcChk`); the pieces of verification
(`VPiece`); and the prologue (`vpro_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece disjW disjW')
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (pro)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params) (σ : State)

abbrev pkOf : List Byte := bytesAt σ.mem (State.addr (VG.Proof.MlDsa.Arm.Verify.vPk σ)) p.pkLen
abbrev muOf : List Byte := bytesAt σ.mem (State.addr (VG.Proof.MlDsa.Arm.Verify.vMu σ)) 64
abbrev sgOf : List Byte := bytesAt σ.mem (State.addr (VG.Proof.MlDsa.Arm.Verify.vSg σ)) p.sigLen

end

/-- The public data of `verifyContract`. -/
def vPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ VG.Proof.MlDsa.Arm.Verify.vPk σ₁ = VG.Proof.MlDsa.Arm.Verify.vPk σ₂ ∧ VG.Proof.MlDsa.Arm.Verify.vMu σ₁ = VG.Proof.MlDsa.Arm.Verify.vMu σ₂ ∧ VG.Proof.MlDsa.Arm.Verify.vSg σ₁ = VG.Proof.MlDsa.Arm.Verify.vSg σ₂ ∧ VG.Proof.MlDsa.Arm.Verify.vScr σ₁ = VG.Proof.MlDsa.Arm.Verify.vScr σ₂ ∧
    VG.Proof.MlDsa.Arm.Verify.pkOf p σ₁ = VG.Proof.MlDsa.Arm.Verify.pkOf p σ₂ ∧ VG.Proof.MlDsa.Arm.Verify.muOf σ₁ = VG.Proof.MlDsa.Arm.Verify.muOf σ₂ ∧ VG.Proof.MlDsa.Arm.Verify.sgOf p σ₁ = VG.Proof.MlDsa.Arm.Verify.sgOf p σ₂

/-- The pieces of verification. -/
abbrev VPiece (p : Params) (STK : Nat) := Piece (VG.Proof.MlDsa.Arm.Verify.VPre p STK) (VG.Proof.MlDsa.Arm.Verify.vPub p)

theorem vlay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : VG.Proof.MlDsa.Arm.Verify.vPub p σ₁ σ₂) : VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁ = VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [VG.Proof.MlDsa.Arm.Verify.vlay, VG.Proof.MlDsa.Arm.Verify.vPk, VG.Proof.MlDsa.Arm.Verify.vMu, VG.Proof.MlDsa.Arm.Verify.vSg, VG.Proof.MlDsa.Arm.Verify.vScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure VC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : VG.Proof.MlKem.Arm.Saved s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872) 32 = σ.gpr .lr
  pk : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 2 0) p.pkLen = VG.Proof.MlDsa.Arm.Verify.pkOf p σ
  mu : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 3 0) 64 = VG.Proof.MlDsa.Arm.Verify.muOf σ
  sg : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 4 0) p.sigLen = VG.Proof.MlDsa.Arm.Verify.sgOf p σ

theorem inputs_eq (p : Params) (STK : Nat) (σ : State) :
    bytesAt σ.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 2 0) p.pkLen = VG.Proof.MlDsa.Arm.Verify.pkOf p σ ∧ bytesAt σ.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 3 0) 64 = VG.Proof.MlDsa.Arm.Verify.muOf σ ∧
      bytesAt σ.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 4 0) p.sigLen = VG.Proof.MlDsa.Arm.Verify.sgOf p σ := by
  simp only [Lay.A, add_ofNat_zero]; exact ⟨rfl, rfl, rfl⟩

/-- A part that writes the regions `W` keeps `VC`. -/
def vcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, 840, 36) W && W.all (fun w => w.1 == 0 || w.1 == 1) &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (2, 0, p.pkLen) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (3, 0, 64) W &&
    sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (4, 0, p.sigLen) W

/-- Bytes of a buffer only read, kept by a part that writes only buffers of `vWb`. -/
theorem bytes_keepR {L : Lay} (hL : OkW L VG.Proof.MlDsa.Arm.Verify.vWb) {W : List (Nat × Nat × Nat)} {m m' : Mem} (hf : Frame (L.RL W) m m')
    {i o l : Nat} (h : sepAll L.sizes (i, o, l) W = true) (hw : W.all (fun w => w.1 == 0 || w.1 == 1) = true)
    (hl : l ≤ 2 ^ 64) : bytesAt m' (L.A i o) l = bytesAt m (L.A i o) l :=
  Proof.MlKem.bytesAt_frame hf (fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
    refine VG.Proof.MlDsa.Arm.KeyGen.disjW hL (List.all_eq_true.mp h w hw') (.inr ?_)
    have := List.all_eq_true.mp hw w hw'
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    simp only [VG.Proof.MlDsa.Arm.Verify.vWb, List.mem_cons, List.not_mem_nil, or_false]
    exact this) hl

theorem vfit {p : Params} {STK : Nat} {σ : State} (hL : OkW (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb) (i : Nat) (hi : i < 5) :
    (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).size i ≤ 2 ^ 64 := by
  have := hL.fit i (by simp only [VG.Proof.MlDsa.Arm.Verify.vlay, List.length_cons, List.length_nil]; omega)
  omega

theorem VC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W = true) : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s' := by
  simp only [VG.Proof.MlDsa.Arm.Verify.vcChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, hw⟩, h2⟩, h3⟩, h4⟩ := hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).RL W, ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr
      exact VG.Proof.MlDsa.Arm.KeyGen.disjW hL (List.all_eq_true.mp h0 w hw') (.inl (by decide))
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW (r := (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.lr
  · rw [VG.Proof.MlDsa.Arm.Verify.bytes_keepR hL hk.frame h2 hw (by have := VG.Proof.MlDsa.Arm.Verify.vfit hL 2 (by decide); exact this)]
    exact h.pk
  · rw [VG.Proof.MlDsa.Arm.Verify.bytes_keepR hL hk.frame h3 hw (by decide)]; exact h.mu
  · rw [VG.Proof.MlDsa.Arm.Verify.bytes_keepR hL hk.frame h4 hw (by have := VG.Proof.MlDsa.Arm.Verify.vfit hL 4 (by decide); exact this)]
    exact h.sg

/-! ## The prologue -/

theorem vpro_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : VG.Proof.MlDsa.Arm.Verify.VPre p STK σ) :
    WP isa (.block VG.Impl.MlDsa.Arm.KeyGen.pro) σ fun s => VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ s.gpr .r11 = 1 := by
  have hL := VG.Proof.MlDsa.Arm.Verify.vlay_ok hp
  have hk := hF.k
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).buf 0 = regA (VG.Proof.MlDsa.Arm.Verify.vScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_singleton_self _
  have eA : ∀ o, (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 o = State.addr (σ.gpr .r3) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by simp only [VG.Proof.MlDsa.Arm.Verify.vlay, Lay.size, List.getD_cons_zero]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [VG.Impl.MlDsa.Arm.KeyGen.pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = VG.Proof.MlDsa.Arm.Verify.vScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872 := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have e1 : encodable (1 : BitVec 32) = true := by decide
  run_block [i872, o1, e1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872) v).readW
      ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega) (by decide)
  have fr : Frame [(VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36] σ.mem (s₁.mem.writeW ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega
    · simp only [Region.Contains, eA]; bv_omega
  have hin : ∀ {i l : Nat}, i ≠ 0 → i < 5 → l = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).size i →
      bytesAt (s₁.mem.writeW ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872) (s₁.gpr .lr)) ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A i 0) l =
        bytesAt σ.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A i 0) l := fun {i l} h0 h5 hl => by
    refine Proof.MlKem.bytesAt_frame fr (fun r hr => ?_) (by rw [hl]; exact VG.Proof.MlDsa.Arm.Verify.vfit hL i h5)
    rw [List.mem_singleton] at hr; subst hr
    refine disjW' (i := i) (o := 0) (l := l) (j := 0) (o' := 840) (l' := 36) hL ?_ (.inr (.inl (by decide)))
    subst hl
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> vsep hF [VG.Proof.MlDsa.Arm.Verify.vlay, Lay.size]
  obtain ⟨ep, em, es⟩ := VG.Proof.MlDsa.Arm.Verify.inputs_eq p STK σ
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by simp only [VG.Proof.MlDsa.Arm.Verify.vlay, Lay.size, List.getD_cons_zero]; omega, rfl,
    show σ.sp - BitVec.ofNat 32 STK = s₁.sp - BitVec.ofNat 32 STK by rw [h₁.sp], hSTK,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [VG.Proof.MlDsa.Arm.Verify.vWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simp [Lay.buf, VG.Proof.MlDsa.Arm.Verify.vlay]
    · exact absurd rfl hi1
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, VG.Proof.MlDsa.Arm.Verify.vlay]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 872 = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 2) (l := p.pkLen) (by decide) (by decide) rfl]; exact ep
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 3) (l := 64) (by decide) (by decide) rfl]; exact em
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, hin (i := 4) (l := p.sigLen) (by decide) (by decide) rfl]; exact es
  · trivial

theorem vpro_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hSTK : 8 ≤ STK) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => s = σ) (fun σ s => VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ s.gpr .r11 = 1) (.block VG.Impl.MlDsa.Arm.KeyGen.pro) :=
  ⟨fun σ s hp hs => by subst hs; exact VG.Proof.MlDsa.Arm.Verify.vpro_ok hF hSTK hp,
    Sample.taint_block [.r0, .r1, .r2, .r3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by taint_decide)⟩

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Control`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: two runs, and the branches

Two runs whose entry states agree on the public data have the same layout
(`vc_twoL`), so that the taint analysis from its pointers checks the parts
without calls (`vtaint7`). A branch on `r11` (`ifOk`) takes the same way in
two runs where `r11` is a function of the public data (`ifOk_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint7 taint4)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs -/

theorem vc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : VG.Proof.MlDsa.Arm.Verify.vPub p σ₁ σ₂) (h₁ : VG.Proof.MlDsa.Arm.Verify.VC p STK σ₁ x)
    (h₂ : VG.Proof.MlDsa.Arm.Verify.VC p STK σ₂ y) : VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁) VG.Proof.MlDsa.Arm.Verify.vWb STK x y :=
  ⟨h₁.site, VG.Proof.MlDsa.Arm.Verify.vlay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- Two runs whose entry states have the same layout. -/
def VTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y

theorem vtaint7 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) : RelCT isa (VG.Proof.MlDsa.Arm.Verify.VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint7 (fun _ _ h => h) h

theorem vtaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa (VG.Proof.MlDsa.Arm.Verify.VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h

/-- A piece without calls, checked by the taint analysis from `scratch`. -/
theorem vrel7 {p : Params} {STK : Nat} {I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.Arm.Verify.VC p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) :
    RelCT isa (Rel2 (VG.Proof.MlDsa.Arm.Verify.VPre p STK) (VG.Proof.MlDsa.Arm.Verify.vPub p) I) c fun _ _ => True :=
  rel_of (VG.Proof.MlDsa.Arm.Verify.vtaint7 h) fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-! ## The state, but for a register or the flags -/

theorem VC.r11 {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) (v : BitVec 32) :
    VG.Proof.MlDsa.Arm.Verify.VC p STK σ (s.setReg .r11 v) :=
  ⟨h.site.setReg (by decide) v, h.rd, h.wr, h.sp, h.sav, h.lr, h.pk, h.mu, h.sg⟩

/-! ## A branch on `r11` -/

theorem cmp11_ok (s : State) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s (· = subFlags s (s.gpr .r11) 0) := by
  apply WP.of_runBlock
  simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

theorem eval_cmp11 (s : State) : isa.eval .ne (subFlags s (s.gpr .r11) 0) = some (decide (s.gpr .r11 ≠ 0)) := by
  show some (!(s.gpr .r11 - 0 == 0)) = _
  rw [show s.gpr .r11 - 0 = s.gpr .r11 from by simp]
  by_cases h : s.gpr .r11 = 0
  · simp [h]
  · rw [beq_eq_false_iff_ne.mpr h]; simp only [Bool.not_false, Option.some.injEq]; exact (decide_eq_true h).symm

/-- `ifOk c`: `c` if `r11 ≠ 0`, where `r11` is `v σ`, a function of the
public data. -/
theorem ifOk_piece {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa} {v : State → BitVec 32}
    (hv : ∀ σ s, VG.Proof.MlDsa.Arm.Verify.VPre p STK σ → I σ s → s.gpr .r11 = v σ)
    (hpub : ∀ σ₁ σ₂, VG.Proof.MlDsa.Arm.Verify.VPre p STK σ₁ → VG.Proof.MlDsa.Arm.Verify.VPre p STK σ₂ → VG.Proof.MlDsa.Arm.Verify.vPub p σ₁ σ₂ → v σ₁ = v σ₂)
    (hI : ∀ σ s (a b : BitVec 32), I σ s → I σ (subFlags s a b))
    (hc : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => I σ s ∧ v σ ≠ 0) J c)
    (he : ∀ σ s, VG.Proof.MlDsa.Arm.Verify.VPre p STK σ → I σ s → v σ = 0 → J σ s) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK I J (ifOk c) := by
  refine ⟨fun σ s hp hs => WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Verify.cmp11_ok s) fun s₁ e₁ => ?_), ?_⟩
  · subst e₁
    have h11 := hv σ s hp hs
    refine WP.ite _ (VG.Proof.MlDsa.Arm.Verify.eval_cmp11 s) (fun hb => hc.ok σ _ hp ⟨hI σ s _ _ hs, ?_⟩) fun hb => ?_
    · rw [← h11]; exact of_decide_eq_true hb
    · have : v σ = 0 := by rw [← h11]; simpa using hb
      exact WP.block_nil (he σ _ hp (hI σ s _ _ hs) this)
  · refine RelCT.seq (R := Rel2 (VG.Proof.MlDsa.Arm.Verify.VPre p STK) (VG.Proof.MlDsa.Arm.Verify.vPub p) fun σ s => ∃ s₀, I σ s₀ ∧ s = subFlags s₀ (s₀.gpr .r11) 0)
      ?_ (RelCT.ite ?_ ?_ ?_)
    · refine relInv (I' := fun σ s => ∃ s₀, I σ s₀ ∧ s = subFlags s₀ (s₀.gpr .r11) 0)
        (fun σ s _ hs => WP.mono (VG.Proof.MlDsa.Arm.Verify.cmp11_ok s) fun s' e => ⟨s, hs, e⟩) ?_
      exact relct_noMem (by decide)
    · rintro _ _ ⟨σ₁, σ₂, p₁, p₂, pub, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
      rw [VG.Proof.MlDsa.Arm.Verify.eval_cmp11, VG.Proof.MlDsa.Arm.Verify.eval_cmp11, hv _ _ p₁ hx, hv _ _ p₂ hy, hpub _ _ p₁ p₂ pub]
    · refine RelCT.mono hc.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨x, hx, e₁⟩, ⟨y, hy, e₂⟩⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨e₁ ▸ hI _ _ _ _ hx, ?_⟩, ⟨e₂ ▸ hI _ _ _ _ hy, ?_⟩⟩) fun _ _ h => h
      · subst e₁; rw [VG.Proof.MlDsa.Arm.Verify.eval_cmp11] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · subst e₁ e₂; rw [VG.Proof.MlDsa.Arm.Verify.eval_cmp11] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb
    · exact RelCT.block_nil fun _ _ _ => trivial

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Hint`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: the primitives, and the hint

The primitives verification calls, verified with at most `S` bytes of stack
(`VPrimsOk`); and the hint `h` of the signature, unpacked to polynomials `0,
…, k - 1`, with `r11` 1 if it is well formed and 0 if not (`hint_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee HbuOk hbu_okS
  hbu_tr)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params HintIs hintBitUnpack)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure VPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Spec.MlDsa.nttContract Arm.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Spec.MlDsa.nttInvContract Arm.abi stk) S
  mul : Callee P.mul (fun stk => Spec.MlDsa.mulContract Arm.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Spec.MlDsa.mulAddContract Arm.abi stk) S
  sub : Callee P.sub (fun stk => Spec.MlDsa.subContract Arm.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Spec.MlDsa.rejNTTContract Arm.abi stk) S
  ball : Callee P.ball (fun stk => Spec.MlDsa.sampleInBallContract Arm.abi stk) S
  useHint : Callee P.useHint (fun stk => Spec.MlDsa.useHintContract Arm.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Spec.MlDsa.simpleBitPackContract Arm.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => Spec.MlDsa.bitUnpackContract Arm.abi stk) S
  unpackT1 : Callee P.unpackT1 (fun stk => Spec.MlDsa.unpackT1Contract Arm.abi stk) S
  hintUnpack : Callee P.hintUnpack (fun stk => Spec.MlDsa.hintBitUnpackContract Arm.abi stk) S
  normLt : Callee P.normLt (fun stk => Spec.MlDsa.normLtContract Arm.abi stk) S

/-- 1 if `b`, 0 if not. -/
def flag (b : Bool) : BitVec 32 := if b then 1 else 0

/-! ## The signature -/

/-- `h`, or `⊥`, of the signature of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)

/-- Bytes of the signature, from its bytes in memory. -/
theorem sig_slice {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.sigLen) :
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 4 o) l = ((VG.Proof.MlDsa.Arm.Verify.sgOf p σ).drop o).take l := by
  have e := h.sg
  simp only [Lay.A, add_ofNat_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-- Bytes of the public key, from its bytes in memory. -/
theorem pk_slice {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.pkLen) :
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 2 o) l = ((VG.Proof.MlDsa.Arm.Verify.pkOf p σ).drop o).take l := by
  have e := h.pk
  simp only [Lay.A, add_ofNat_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-! ## The hint -/

/-- After the hint. -/
structure V1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s
  r11 : s.gpr .r11 = VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.hintOf p σ).isSome
  hint : ∀ h, VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h → HintIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem hint_m {σ : State} :
    VG.Proof.MlDsa.Arm.KeyGen.HbuOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (.r6, oHint p) (p.ω + p.k) p.ω (VG.Impl.MlDsa.Arm.Verify.pH 0) (256 * p.k) := by
  have hk := hF.k; have hom := hF.om
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF,
    by rw [Nat.add_sub_cancel_left]; exact hF.hp, by omega, by rw [Nat.add_sub_cancel_left], by omega⟩

/-- After the call of `HintBitUnpack`: its result in `r0`. -/
structure H1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.hintOf p σ).isSome
  hint : ∀ h, VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h → HintIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h

theorem hbu_ok' {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) :
    WP isa (hintUnpackAt P (.r6, oHint p) (p.ω + p.k) p.ω (VG.Impl.MlDsa.Arm.Verify.pH 0) (256 * p.k)) s (VG.Proof.MlDsa.Arm.Verify.H1 p STK σ) := by
  have hs := h.site
  unfold hintUnpackAt
  refine VG.Proof.MlDsa.Arm.KeyGen.hbu_okS hP.hintUnpack hs (by omega) (VG.Proof.MlDsa.Arm.Verify.hint_m hF) fun s' k' hm => ?_
  have h' := h.keep k' (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk])
  have eb : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, oHint p)) (p.ω + p.k) =
      ((VG.Proof.MlDsa.Arm.Verify.sgOf p σ).drop (oHint p)).take (p.ω + p.k) := VG.Proof.MlDsa.Arm.Verify.sig_slice h (by rw [hF.sig])
  rw [eb, Nat.add_sub_cancel_left] at hm
  refine ⟨h', ?_, fun hh e => ?_⟩
  · show s'.gpr .r0 = VG.Proof.MlDsa.Arm.Verify.flag (VG.Spec.MlDsa.hintBitUnpack p.ω p.k (((VG.Proof.MlDsa.Arm.Verify.sgOf p σ).drop (oHint p)).take (p.ω + p.k))).isSome
    split at hm
    · rename_i hh e; rw [e]; exact hm.1
    · rename_i e; rw [e]; exact hm
  · show HintIs s'.mem _ p.k hh
    have e' : VG.Spec.MlDsa.hintBitUnpack p.ω p.k ((VG.Proof.MlDsa.Arm.Verify.sgOf p σ).drop (oHint p) |>.take (p.ω + p.k)) = some hh := e
    rw [e'] at hm
    exact hm.2

theorem hbu_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ s.gpr .r11 = 1) (VG.Proof.MlDsa.Arm.Verify.H1 p STK)
      (hintUnpackAt P (.r6, oHint p) (p.ω + p.k) p.ω (VG.Impl.MlDsa.Arm.Verify.pH 0) (256 * p.k)) := by
  refine ⟨fun σ s _ h => VG.Proof.MlDsa.Arm.Verify.hbu_ok' hP hF hS h.1, ?_⟩
  unfold hintUnpackAt
  refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
    bytesAt x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, oHint p)) (p.ω + p.k))
    (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.hbu_tr hP.hintUnpack (by omega) (VG.Proof.MlDsa.Arm.Verify.hint_m hF)
      fun x y ⟨T, e⟩ => ⟨T.1, T.2.1, T.2.2, e⟩) ?_
  intro σ₁ _ _ _ _ _ pub h₁ h₂
  refine ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.1 h₂.1, ?_⟩
  show bytesAt _ ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁).A 4 (oHint p)) _ = bytesAt _ ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁).A 4 (oHint p)) _
  rw [VG.Proof.MlDsa.Arm.Verify.sig_slice h₁.1 (by rw [hF.sig]), pub.2.2.2.2.2.2.2, VG.Proof.MlDsa.Arm.Verify.vlay_pub pub, VG.Proof.MlDsa.Arm.Verify.sig_slice h₂.1 (by rw [hF.sig])]

omit hP hF hS in
theorem mov11_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.H1 p STK) (VG.Proof.MlDsa.Arm.Verify.V1 p STK) (.block [.mov .r11 (.reg .r0)]) := by
  refine ⟨fun σ s _ h => ?_, VG.Proof.MlDsa.Arm.Verify.vrel7 (fun _ _ h => h.vc) (by taint_decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨h.vc.r11 _, by rw [gpr_setReg_self]; exact h.r0, h.hint⟩

theorem hint_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ s.gpr .r11 = 1) (VG.Proof.MlDsa.Arm.Verify.V1 p STK) (hint P p) :=
  (VG.Proof.MlDsa.Arm.Verify.hbu_piece hP hF hS).seq VG.Proof.MlDsa.Arm.Verify.mov11_piece

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Z`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: `z`

Once the hint is well formed: each `z[i]`, unpacked from the signature to
polynomial `8 + i`, and its norm checked, with `r11` 1 exactly when every
`‖z[i]‖∞` so far is less than `γ₁ - β` (`V2`, `zOne_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BuOk bu_okS
  bu_tr nl_ok nl_tr polyIs_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced)
open VG.Proof.MlDsa.Verify (vZ)
open VG.Spec.Sha3 (bytesAt)

/-- `‖z[i]‖∞ < γ₁ - β` for every `i < j`. -/
abbrev zOk (p : Params) (σ : State) (j : Nat) : Bool :=
  decide (∀ i < j, normRq [toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i)] < p.γ₁ - p.β)

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o k : Nat} (h : sepAll L.sizes (i, o, 1024 * k) W = true) (hw : i ∈ Wb)
    (hk : 1024 * k ≤ 2 ^ 64) {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) k hh) :
    HintIs m' (L.A i o) k hh :=
  Proof.MlDsa.Verify.hintIs_frame hf hk (keepD hL h hw) hi

/-- After the hint and the first `j` of `z`. -/
structure V2 (p : Params) (STK : Nat) (j : Nat) (σ s : State) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s
  hint : ∃ h, VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h ∧ HintIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < j, PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i))
  r11 : s.gpr .r11 = VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.zOk p σ j)

theorem V2.keep {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK j : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Verify.V2 p STK j σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < j, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true)
    (h11 : s'.gpr .r11 = s.gpr .r11) : VG.Proof.MlDsa.Arm.Verify.V2 p STK j σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, VG.Proof.MlDsa.Arm.Verify.hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'), by rw [h11]; exact h.r11⟩

theorem flag_and (a b : Bool) : VG.Proof.MlDsa.Arm.Verify.flag a &&& VG.Proof.MlDsa.Arm.Verify.flag b = VG.Proof.MlDsa.Arm.Verify.flag (a && b) := by
  cases a <;> cases b <;> decide

theorem zOk_succ (p : Params) (σ : State) (j : Nat) :
    VG.Proof.MlDsa.Arm.Verify.zOk p σ (j + 1) = (VG.Proof.MlDsa.Arm.Verify.zOk p σ j && decide (normRq [toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) j)] < p.γ₁ - p.β)) := by
  simp only [VG.Proof.MlDsa.Arm.Verify.zOk]
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr (Iff.intro (fun h => ⟨fun i hi => h i (by omega), h j (by omega)⟩) fun h i hi => ?_)
  rcases (by omega : i < j ∨ i = j) with hi | rfl
  exacts [h.1 i hi, h.2]

/-! ## One `z[i]` -/

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem bu_m {σ : State} {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.KeyGen.BuOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (.r6, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j) := by
  have hl := hF.l
  obtain ⟨hb, hlz, hg⟩ := hF.bu
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, ?_, hb, hlz, ?_⟩
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> rw [e] <;> omega

/-- After `z[j]` is unpacked. -/
abbrev Z1 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Verify.V2 p STK j σ s ∧ PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (8 + j))) (toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) j))

theorem bu_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.V2 p STK j) (VG.Proof.MlDsa.Arm.Verify.Z1 p STK j)
      (bitUnpackAt P (.r6, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold bitUnpackAt
    refine VG.Proof.MlDsa.Arm.KeyGen.bu_okS hP.bitUnpack h.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.bu_m hF hj) fun s' k' hz => ⟨h.keep hF k' ?_ ?_ ?_
      (k'.cs .r11 (by decide) (by decide)), ?_⟩
    · rcases hF.lz with e | e <;> vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk, hF.sig, hF.hint, e]
    · vsep hF
    · intro i hi; vsep hF
    · have e : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, p.ctildeLen + lenZ p * j)) (lenZ p) =
          ((VG.Proof.MlDsa.Arm.Verify.sgOf p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p) :=
        VG.Proof.MlDsa.Arm.Verify.sig_slice h.vc (by rw [hF.sig, hF.hint]; rcases hF.lz with e | e <;> rw [e] <;> omega)
      rw [e] at hz
      exact hz
  · unfold bitUnpackAt
    exact rel_of (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.bu_tr hP.bitUnpack (by omega) (VG.Proof.MlDsa.Arm.Verify.bu_m hF hj) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc⟩

/-- After the norm of `z[j]`. -/
abbrev Z2 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Verify.Z1 p STK j σ s ∧ s.gpr .r0 = VG.Proof.MlDsa.Arm.Verify.flag (decide (normRq [toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) j)] < p.γ₁ - p.β))

theorem nl_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.Z1 p STK j) (VG.Proof.MlDsa.Arm.Verify.Z2 p STK j) (normLtAt P (pZ j) (p.γ₁ - p.β)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold normLtAt
    have hr0 : Reduced s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)) := h.2.1
    have pf : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j) 1024 := ⟨rfl, by vsep hF⟩
    have hb : p.γ₁ - p.β < 2 ^ 32 := hF.nb.1
    refine VG.Proof.MlDsa.Arm.KeyGen.nl_ok hP.normLt h.1.vc.site (by omega) (bd := p.γ₁ - p.β) pf hb hr0 fun s' k' hr => ⟨⟨h.1.keep hF k'
      (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF) (k'.cs .r11 (by decide) (by decide)),
      polyIs_keepW h.1.vc.site.ok k'.frame (by vsep hF) (by decide) rfl h.2⟩, ?_⟩
    rw [hr, show polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)) = _ from h.2.2, VG.Proof.MlDsa.Arm.Verify.flag]
    simp only [decide_eq_true_eq]
  · unfold normLtAt
    refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.nl_tr hP.normLt (by omega) (bd := p.γ₁ - p.β)
        (⟨rfl, by vsep hF⟩ : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j) 1024) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ?_
    have r₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pZ j)) := h₂.2.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at r₂
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.1.vc h₂.1.vc, h₁.2.1, r₂⟩

omit hP hF hS in
theorem and11_piece {j : Nat} : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.Z2 p STK j) (VG.Proof.MlDsa.Arm.Verify.V2 p STK (j + 1)) (.block and11) := by
  refine ⟨fun σ s _ h => ?_, VG.Proof.MlDsa.Arm.Verify.vrel7 (fun _ _ h => h.1.1.vc) (by taint_decide)⟩
  apply WP.of_runBlock
  simp only [and11, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨h.1.1.vc.r11 _, h.1.1.hint, fun i hi => ?_, ?_⟩
  · rcases (by omega : i < j ∨ i = j) with hi | rfl
    exacts [h.1.1.z i hi, h.1.2]
  · rw [gpr_setReg_self, h.1.1.r11, h.2, VG.Proof.MlDsa.Arm.Verify.flag_and, VG.Proof.MlDsa.Arm.Verify.zOk_succ]

theorem zOne_piece {j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.V2 p STK j) (VG.Proof.MlDsa.Arm.Verify.V2 p STK (j + 1)) (zOne P p j) :=
  (VG.Proof.MlDsa.Arm.Verify.bu_piece hP hF hS hj).seq ((VG.Proof.MlDsa.Arm.Verify.nl_piece hP hF hS hj).seq VG.Proof.MlDsa.Arm.Verify.and11_piece)

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampA`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: the entries of `Â`

Once the hint is well formed and `z` small (`VB`): `ρ` to the seed, and each
entry `Â[r, s]`, `RejNTTPoly(ρ ‖ s ‖ r)`, masked by its result (`aOne_piece`):
after the entries before `(r, c)` in row order (`VS`), each is reduced, and
`r11` is 1 if every sampler succeeded, with the entries those of the standard
for some bound, and 0 if one of them fails within the least bound.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee RnOk rn_ok
  rn_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD setB_ok copyS andMask_ok masked_poly seedA_eq
  taint7)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11 mask setB seqR sampled)
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced rejNTTPoly minBounds Outcome)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## After the checks of the signature -/

/-- The hint well formed and `z` small, in memory. -/
structure VB (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s
  hint : ∃ h, VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h ∧ HintIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i))
  zok : VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ = true

theorem VB.keep {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Verify.VB p STK σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true) :
    VG.Proof.MlDsa.Arm.Verify.VB p STK σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, VG.Proof.MlDsa.Arm.Verify.hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'), h.zok⟩

theorem VB.r11 {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VB p STK σ s) (v : BitVec 32) :
    VG.Proof.MlDsa.Arm.Verify.VB p STK σ (s.setReg .r11 v) :=
  ⟨h.vc.r11 v, h.hint, h.z, h.zok⟩

/-- The entry `(r', s')` comes before `(r, c)`. -/
abbrev Dn (r c r' s' : Nat) : Prop := r' < r ∨ (r' = r ∧ s' < c)

/-- The address of `Â[r, s]`. -/
abbrev aA (p : Params) (STK : Nat) (σ : State) (r s : Nat) : Addr := (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (20 + 8 * r + s))

/-- After the entries of `Â` before `(r, c)`. -/
structure VS (p : Params) (STK : Nat) (r c : Nat) (σ s : State) : Prop where
  vb : VG.Proof.MlDsa.Arm.Verify.VB p STK σ s
  rho : bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 = vRho (VG.Proof.MlDsa.Arm.Verify.pkOf p σ)
  red : ∀ r' s', s' < p.ℓ → VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' → Reduced s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s')
  ok : ∃ q : Bool, s.gpr .r11 = VG.Proof.MlDsa.Arm.Verify.flag q ∧
    (q = true → ∀ r' s', s' < p.ℓ → VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' →
      ∃ b : Nat, rejNTTPoly b (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r' s') = some (polyAt s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s'))) ∧
    (q = false → ∃ r' s', s' < p.ℓ ∧ VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' ∧ rejNTTPoly minBounds.rejNTT (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r' s') = none)

theorem Dn.lt {r c r' s' : Nat} (hd : VG.Proof.MlDsa.Arm.Verify.Dn r c r' s') (hs : s' < 8) (hc : c ≤ 8) : 8 * r' + s' < 8 * r + c ∧ r' ≤ r := by
  rcases hd with h | ⟨rfl, h⟩ <;> omega

theorem flag_and01 (q : Bool) {r : BitVec 32} (hr : r = 0 ∨ r = 1) : VG.Proof.MlDsa.Arm.Verify.flag q &&& r = VG.Proof.MlDsa.Arm.Verify.flag (q && decide (r = 1)) := by
  rcases hr with rfl | rfl <;> cases q <;> decide

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-! ## `ρ` to the seed -/

omit hP hS in
theorem rho_ok {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VB p STK σ s) (h11 : s.gpr .r11 = 1) :
    WP isa (copy .r4 0 .r7 oSB 32) s (VG.Proof.MlDsa.Arm.Verify.VS p STK 0 0 σ) := by
  have hk := hF.k; have hl := hF.l
  refine WP.mono (copyS h.vc.site (sb := .r4) (so := 0) (db := .r7) (dO := oSB) (len := 32) ⟨rfl, by vsep hF⟩
    ⟨rfl, by vsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by vsep hF))
    fun s' ⟨k', b'⟩ => ⟨h.keep hF k' (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF), ?_,
      fun _ _ _ hd => absurd hd (by omega), ⟨true, by rw [k'.cs .r11 (by decide) (by decide), h11]; rfl,
        fun _ _ _ _ hd => absurd hd (by omega), fun h => absurd h (by decide)⟩⟩
  show bytesAt s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r7, oSB)) 32 = _
  rw [b', show lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r4, 0) = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 2 0 from rfl, VG.Proof.MlDsa.Arm.Verify.pk_slice h.vc (by rw [hF.pk]; omega),
    List.drop_zero]
  rfl

/-! ## One entry -/

omit hP hS in
theorem rn_m {σ : State} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    RnOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (sc oSB) (pS (20 + (8 * r + c))) (sc oSS) := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide,
    show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF, by vsep hF, by vsep hF⟩

theorem aOne_ok {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VS p STK r c σ s) :
    WP isa (aOne P (8 * r + c)) s (VG.Proof.MlDsa.Arm.Verify.VS p STK r (c + 1) σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold aOne sampled
  have e8 : (8 * r + c) % 8 = c := by omega
  have e8' : (8 * r + c) / 8 = r := by omega
  rw [e8, e8']
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨rfl, by vsep hF⟩ (by decide)
    (by decide) c) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSB + 33)) ⟨rfl, by vsep hF⟩
      (by decide) (by decide) r) fun s₂ ⟨k₂, b₂⟩ => ?_))
  have kv := (h.vb.keep hF k₁ (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF)).keep hF k₂
    (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have hseed : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 34 = aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r c := by
    have b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho)
    have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
      add_ofNat_add, add_ofNat_add, show aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r c = _ from seedA_eq (vRho (VG.Proof.MlDsa.Arm.Verify.pkOf p σ)) r c,
      List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oSB + 32 + 1)) 1 = [BitVec.ofNat 8 r] := b₂
    rw [e1, e2]; rfl
  have kept12 : ∀ r' s', s' < p.ℓ → VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' → polyAt s₂.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') = polyAt s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') ∧
      (Reduced s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') → Reduced s₂.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨(polyAt_keepW hL k₂.frame (by vsep hF) (by decide) rfl).trans (polyAt_keepW hL k₁.frame (by vsep hF) (by decide) rfl),
      fun hr' => reduced_keepW hL k₂.frame (by vsep hF) (by decide) rfl (reduced_keepW hL k₁.frame (by vsep hF)
        (by decide) rfl hr')⟩
  have h11₂ : s₂.gpr .r11 = s.gpr .r11 := by rw [k₂.cs .r11 (by decide) (by decide), k₁.cs .r11 (by decide) (by decide)]
  -- the call
  refine WP.seq (rn_ok hP.rejNtt kv.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.rn_m hF hr hc) fun s₃ k₃ hred hout => ?_)
  have hseed' : bytesAt s₂.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc oSB)) 34 = _ := hseed
  rw [hseed'] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := kv.keep hF k₃ (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kept3 : ∀ r' s', s' < p.ℓ → VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' → polyAt s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') = polyAt s₂.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') ∧
      (Reduced s₂.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') → Reduced s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl hr'⟩
  have rho₃ : bytesAt s₃.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 = vRho (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) :=
    (bytes_keepW hL k₃.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
        ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho))
  have h11₃ : s₃.gpr .r11 = s.gpr .r11 := by rw [k₃.cs .r11 (by decide) (by decide), h11₂]
  -- the result and the mask
  refine WP.mono (andMask_ok kv₃.vc.site (a := pS (20 + (8 * r + c))) ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) hr01) fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.r11 (s₃.gpr .r11 &&& s₃.gpr .r0)).keep hF k₄ (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF)
    (fun i hi => by vsep hF)
  have kept4 : ∀ r' s', s' < p.ℓ → VG.Proof.MlDsa.Arm.Verify.Dn r c r' s' → polyAt s₄.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') = polyAt s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') ∧
      (Reduced s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s') → Reduced s₄.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl hr'⟩
  have ea : lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pS (20 + (8 * r + c))) = VG.Proof.MlDsa.Arm.Verify.aA p STK σ r c := by
    show (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (20 + (8 * r + c))) = _
    rw [← Nat.add_assoc]
  rw [ea] at pi p1 hout
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, (bytes_keepW hL k₄.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans rho₃,
    fun r' s' hs' hd => ?_, ⟨q && decide (s₃.gpr .r0 = 1), ?_, fun hq' r' s' hs' hd => ?_, fun hq' => ?_⟩⟩
  · have := hd.lt (by omega) (by omega)
    rcases (by omega : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · exact (kept4 r' s' hs' hd).2 ((kept3 r' s' hs' hd).2 ((kept12 r' s' hs' hd).2 (h.red r' s' hs' hd)))
    · exact pi.1
  · rw [r₄, h11₃, hq, VG.Proof.MlDsa.Arm.Verify.flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    rcases (by omega : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · obtain ⟨b, hb⟩ := hok hq'.1 r' s' hs' hd
      refine ⟨b, ?_⟩
      rw [(kept4 r' s' hs' hd).1, (kept3 r' s' hs' hd).1, (kept12 r' s' hs' hd).1]
      exact hb
    · rw [p1 hq'.2]
      rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
      · exact ⟨b.rejNTT, hb⟩
      · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r', s', hs', hd, hn⟩ := hbad hq'
      exact ⟨r', s', hs', by omega, hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact ⟨r, c, hc, by omega, hn⟩

/-! ## Constant time -/

omit hP hF hS in
theorem vsetB2_taint : ∀ v < 8, ∀ w < 8, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc (oSB + 32)) v ++ setB (sc (oSB + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem vAndMask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem aOne_two {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) (σ : State) :
    RelCT isa (fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32) (aOne P (8 * r + c))
      fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  unfold aOne sampled
  have e8 : (8 * r + c) % 8 = c := by omega
  have e8' : (8 * r + c) / 8 = r := by omega
  rw [e8, e8']
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 34 = bytesAt x.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 ++
      [BitVec.ofNat 8 c, BitVec.ofNat 8 r]
  have hF1 : ∀ x, Site (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x →
      WP isa (.block (setB (sc (oSB + 32)) c ++ setB (sc (oSB + 33)) r)) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨rfl, by vsep hF⟩ (by decide) (by decide) c)
      fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSB + 33)) ⟨rfl, by vsep hF⟩
        (by decide) (by decide) r) fun s₂ ⟨k₂, b₂⟩ => ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSB + 32)) 1,
          tri (sc (oSB + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩, by
        have hL := hs.ok
        have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
        have b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oSB + 32 + 1)) 1 = [BitVec.ofNat 8 r] := b₂
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32)
    (taint7 (fun _ _ h => h.1) (VG.Proof.MlDsa.Arm.Verify.vsetB2_taint _ (by omega) _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
        bytesAt x.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 34 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (hs : Site (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x) =>
    rn_ok hP.rejNtt hs (by omega) (name := "vg_mldsa_rej_ntt_poly") (VG.Proof.MlDsa.Arm.Verify.rn_m hF (σ := σ) hr hc)
      (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (VG.Proof.MlDsa.Arm.KeyGen.RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt (by omega) (VG.Proof.MlDsa.Arm.Verify.rn_m hF hr hc)
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (VG.Proof.MlDsa.Arm.Verify.vAndMask_taint _ (by omega))

theorem aOne_piece {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.VS p STK r c) (VG.Proof.MlDsa.Arm.Verify.VS p STK r (c + 1)) (aOne P (8 * r + c)) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.aOne_ok hP hF hS hr hc h,
    rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      bytesAt x.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oSB) 32)
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.Verify.aOne_two hP hF hS hr hc σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
        ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vb.vc h₂.vb.vc, by rw [h₁.rho, VG.Proof.MlDsa.Arm.Verify.vlay_pub pub, h₂.rho, pub.2.2.2.2.2.1]⟩⟩

/-! ## The rows -/

omit hP hF hS in
theorem VS.next {r : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VS p STK r p.ℓ σ s) : VG.Proof.MlDsa.Arm.Verify.VS p STK (r + 1) 0 σ s := by
  have e : ∀ r' s', s' < p.ℓ → (VG.Proof.MlDsa.Arm.Verify.Dn (r + 1) 0 r' s' ↔ VG.Proof.MlDsa.Arm.Verify.Dn r p.ℓ r' s') := fun r' s' hs => by
    simp only [VG.Proof.MlDsa.Arm.Verify.Dn]; omega
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  exact ⟨h.vb, h.rho, fun r' s' hs hd => h.red r' s' hs ((e r' s' hs).mp hd),
    ⟨q, hq, fun hq' r' s' hs hd => hok hq' r' s' hs ((e r' s' hs).mp hd),
      fun hq' => let ⟨r', s', hs, hd, hn⟩ := hbad hq'; ⟨r', s', hs, (e r' s' hs).mpr hd, hn⟩⟩⟩

theorem aRow_piece {r : Nat} (hr : r < p.k) : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.VS p STK r 0) (VG.Proof.MlDsa.Arm.Verify.VS p STK (r + 1) 0) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine Piece.mono (Piece.seqR (I := fun e σ s => VG.Proof.MlDsa.Arm.Verify.VS p STK r (e - 8 * r) σ s) p.ℓ (8 * r)
    fun e h1 h2 => ?_) (fun σ s _ h => by simpa using h) fun σ s _ h => VS.next (by simpa using h)
  have := VG.Proof.MlDsa.Arm.Verify.aOne_piece hP hF hS hr (c := e - 8 * r) (by omega)
  rw [show 8 * r + (e - 8 * r) = e by omega, show e - 8 * r + 1 = e + 1 - 8 * r by omega] at this
  exact this

theorem rows_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.VS p STK 0 0) (VG.Proof.MlDsa.Arm.Verify.VS p STK p.k 0) (seqR (aRow P p) 0 p.k) := by
  refine Piece.mono (Piece.seqR (I := fun r => VG.Proof.MlDsa.Arm.Verify.VS p STK r 0) p.k 0 fun r _ hr => VG.Proof.MlDsa.Arm.Verify.aRow_piece hP hF hS (by omega))
    (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampC`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: `c`, and the samplers

`c = SampleInBall(c̃)`, masked by its result (`ball_piece`); and the samplers
from the checks of the signature (`samples_piece`): after them (`VS4`), `Â`
and `c` are reduced, and `r11` is 1 if every sampler succeeded, with them
those of the standard for some bounds, and 0 if one fails within the least
bounds.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BallOk ball_okS
  ball_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD andMask_ok masked_poly taint7)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11 mask setB seqR sampled)
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced rejNTTPoly minBounds Outcome sampleInBall)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed vCt)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers. -/
structure VS4 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vb : VG.Proof.MlDsa.Arm.Verify.VB p STK σ s
  red : ∀ r < p.k, ∀ s' < p.ℓ, Reduced s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s')
  redC : Reduced s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 15))
  ok : ∃ q : Bool, s.gpr .r11 = VG.Proof.MlDsa.Arm.Verify.flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ,
      ∃ b : Nat, rejNTTPoly b (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r s') = some (polyAt s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s'))) ∧
      ∃ b : Nat, (VG.Spec.MlDsa.sampleInBall p.τ b (vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ))).map toRq = some (polyAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 15)))) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r s') = none) ∨
      VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)) = none)

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} :
    VG.Proof.MlDsa.Arm.KeyGen.BallOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (.r6, 0) p.ctildeLen p.τ VG.Impl.MlDsa.Arm.Verify.pC (sc oSS) := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide,
    show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF, by vsep hF, by vsep hF, hF.ball.1,
    ⟨by rcases hF.ct with e | e | e <;> omega, by rcases hF.ct with e | e | e <;> omega, hF.ball.2⟩⟩

theorem ball_ok {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VS p STK p.k 0 σ s) :
    WP isa (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ VG.Impl.MlDsa.Arm.Verify.pC) VG.Impl.MlDsa.Arm.Verify.pC) s (VG.Proof.MlDsa.Arm.Verify.VS4 p STK σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold sampled ballAt
  refine WP.seq (VG.Proof.MlDsa.Arm.KeyGen.ball_okS hP.ball hs (by omega) (VG.Proof.MlDsa.Arm.Verify.ball_m hF) fun s₃ k₃ hred hout => ?_)
  have eb : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, 0)) p.ctildeLen = vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) := by
    have := VG.Proof.MlDsa.Arm.Verify.sig_slice h.vb.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  rw [eb] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := h.vb.keep hF k₃ (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA3 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') = polyAt s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') ∧
      (Reduced s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') → Reduced s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl⟩
  have h11₃ : s₃.gpr .r11 = s.gpr .r11 := k₃.cs .r11 (by decide) (by decide)
  refine WP.mono (andMask_ok kv₃.vc.site (a := VG.Impl.MlDsa.Arm.Verify.pC) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.r11 (s₃.gpr .r11 &&& s₃.gpr .r0)).keep hF k₄ (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]) (by vsep hF)
    (fun i hi => by vsep hF)
  have kA4 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₄.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') = polyAt s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') ∧
      (Reduced s₃.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') → Reduced s₄.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl⟩
  have dn : ∀ r s', s' < p.ℓ → (VG.Proof.MlDsa.Arm.Verify.Dn p.k 0 r s' ↔ r < p.k) := fun r s' _ => by simp only [VG.Proof.MlDsa.Arm.Verify.Dn]; omega
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, fun r hr s' hs' => (kA4 r hr s' hs').2 ((kA3 r hr s' hs').2 (h.red r s' hs' ((dn r s' hs').mpr hr))),
    pi.1, ⟨q && decide (s₃.gpr .r0 = 1), ?_, fun hq' => ⟨fun r hr s' hs' => ?_, ?_⟩, fun hq' => ?_⟩⟩
  · rw [r₄, h11₃, hq, VG.Proof.MlDsa.Arm.Verify.flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    obtain ⟨b, hb⟩ := hok hq'.1 r s' hs' ((dn r s' hs').mpr hr)
    exact ⟨b, by rw [(kA4 r hr s' hs').1, (kA3 r hr s' hs').1]; exact hb⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    show ∃ b, _ = some (polyAt s₄.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC))
    rw [p1 hq'.2]
    rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · exact ⟨b.ball, hb⟩
    · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r, s', hs', hd, hn⟩ := hbad hq'
      exact .inl ⟨r, (dn r s' hs').mp hd, s', hs', hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact .inr (Option.map_eq_none_iff.mp hn)

omit hP hF hS in
theorem ballTail_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP 15))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true :=
  VG.Proof.MlDsa.Arm.Verify.vAndMask_taint 15 (by decide)

theorem ball_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.VS p STK p.k 0) (VG.Proof.MlDsa.Arm.Verify.VS4 p STK) (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ VG.Impl.MlDsa.Arm.Verify.pC) VG.Impl.MlDsa.Arm.Verify.pC) := by
  have hk := hF.k
  refine ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.ball_ok hP hF hS h, ?_⟩
  unfold sampled ballAt
  refine RelCT.seq (R := VG.Proof.MlDsa.Arm.Verify.VTwo p STK) ?_ (VG.Proof.MlDsa.Arm.Verify.vtaint7 VG.Proof.MlDsa.Arm.Verify.ballTail_taint)
  refine RelCT.mono (M := isa) (P := fun (x y : State) => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
    bytesAt x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, 0)) p.ctildeLen = bytesAt y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, 0)) p.ctildeLen)
    (RelCT.exists_ fun σ => ?_) (fun _ _ ⟨σ₁, _, _, _, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
  · have ok := fun x (hs : Site (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x) => VG.Proof.MlDsa.Arm.KeyGen.ball_okS hP.ball hs (by omega)
      (name := "vg_mldsa_sample_in_ball") (VG.Proof.MlDsa.Arm.Verify.ball_m hF (σ := σ)) (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
    exact (VG.Proof.MlDsa.Arm.KeyGen.RelCT.two (fun _ _ h => h.1)
      (VG.Proof.MlDsa.Arm.KeyGen.ball_tr hP.ball (by omega) (VG.Proof.MlDsa.Arm.Verify.ball_m hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun x hs => ok x hs).mono (fun _ _ h => h) fun x y h => ⟨σ, h⟩
  · refine ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vb.vc h₂.vb.vc, ?_⟩
    show bytesAt _ ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁).A 4 0) _ = bytesAt _ ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ₁).A 4 0) _
    rw [VG.Proof.MlDsa.Arm.Verify.sig_slice h₁.vb.vc (by have := hF.sig; have := hF.hint; omega), pub.2.2.2.2.2.2.2, VG.Proof.MlDsa.Arm.Verify.vlay_pub pub,
      VG.Proof.MlDsa.Arm.Verify.sig_slice h₂.vb.vc (by have := hF.sig; have := hF.hint; omega)]

/-! ## The samplers -/

omit hP hS in
theorem rho_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.Verify.V2 p STK p.ℓ σ s ∧ VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ) ≠ 0) (VG.Proof.MlDsa.Arm.Verify.VS p STK 0 0) (copy .r4 0 .r7 oSB 32) := by
  refine ⟨fun σ s _ ⟨h, hn⟩ => ?_, rel_of (VG.Proof.MlDsa.Arm.Verify.vtaint4 (by taint_decide)) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.1.vc h₂.1.vc⟩⟩
  have hz : VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ = true := by
    cases e : VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ
    · rw [e] at hn; exact absurd rfl hn
    · rfl
  exact VG.Proof.MlDsa.Arm.Verify.rho_ok hF ⟨h.vc, h.hint, h.z, hz⟩ (by rw [h.r11, hz]; rfl)

theorem samples_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.Verify.V2 p STK p.ℓ σ s ∧ VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ) ≠ 0) (VG.Proof.MlDsa.Arm.Verify.VS4 p STK) (samples P p) :=
  (VG.Proof.MlDsa.Arm.Verify.rho_piece hF).seq ((VG.Proof.MlDsa.Arm.Verify.rows_piece hP hF hS).seq (VG.Proof.MlDsa.Arm.Verify.ball_piece hP hF hS))

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Compute`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: after the samplers

Once the samplers are done, with `Â` and `c` in memory as `A'` and `cc` and
`r11` as `R`, the rest of the function computes `w′₁` from them, whatever they
are (`KC5`): the first `nz` of `z` in the NTT domain, `c` in it or not, and
the first `nr` rows of `w′₁` packed to `B`. Here: `ẑ[j] = NTT(z[j])` and `ĉ =
NTT(c)` (`nttZ_piece`, `nttC_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt Reduced ntt simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- What the samplers give, with `R` their result: `A'` and `cc` those of the
standard for some bounds if `R` is 1, and a sampler failing within the least
bounds if 0. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly) (R : BitVec 32) : Prop :=
  ∃ q : Bool, R = VG.Proof.MlDsa.Arm.Verify.flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ, ∃ b : Nat,
      Spec.MlDsa.rejNTTPoly b (Proof.MlDsa.Verify.aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r s') = some (A' r s')) ∧
      ∃ b : Nat, (Spec.MlDsa.sampleInBall p.τ b (Proof.MlDsa.Verify.vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ))).map toRq = some cc) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
      (Proof.MlDsa.Verify.aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r s') = none) ∨
      Spec.MlDsa.sampleInBall p.τ Spec.MlDsa.minBounds.ball (Proof.MlDsa.Verify.vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)) = none)

/-- After the samplers: `w′₁` from `A'` and `cc`, so far. -/
structure KC5 (p : Params) (STK : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) (R : BitVec 32) (nz : Nat) (nc : Bool) (nr : Nat) (s : State) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s
  hh : VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h
  hint : HintIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r s') (A' r s')
  z : ∀ i < p.ℓ, PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP (8 + i)))
    (if i < nz then zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i else toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i))
  c : PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 15)) (if nc then VG.Spec.MlDsa.ntt cc else cc)
  rows : ∀ r < nr, bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oB + w1Len p * r)) (w1Len p) =
    VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) h r) (w1Max p)
  r11 : s.gpr .r11 = R
  gd : VG.Proof.MlDsa.Arm.Verify.Gd p σ A' cc R

/-- A part that writes `W` keeps what `KC5` says of the polynomials it does not write. -/
structure K5Chk (p : Params) (STK : Nat) (nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  vc : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W = true
  hint : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true
  a : ∀ r < p.k, ∀ s' < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (20 + 8 * r + s'), 1024) W = true
  z : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true
  c : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 15, 1024) W = true
  rows : ∀ r < nr, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oB + w1Len p * r, w1Len p) W = true

/-- Proves a `K5Chk`, in each case of `w1Len`. -/
syntax "k5chk " term:max : tactic
macro_rules
  | `(tactic| k5chk $hF) => `(tactic| (
      rcases ($hF).w1l with hw1 | ⟨hw1, _⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep $hF [vcChk, hw1]))

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : sepAll sz a W₁ = true) (h₂ : sepAll sz a W₂ = true) : sepAll sz a (W₁ ++ W₂) = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

theorem vcChk_append {p : Params} {STK : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W₁ = true)
    (h₂ : VG.Proof.MlDsa.Arm.Verify.vcChk p STK W₂ = true) : VG.Proof.MlDsa.Arm.Verify.vcChk p STK (W₁ ++ W₂) = true := by
  simp only [VG.Proof.MlDsa.Arm.Verify.vcChk, List.all_append, Bool.and_eq_true] at *
  exact ⟨⟨⟨⟨VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.1.1.1.1 h₂.1.1.1.1, h₁.1.1.1.2, h₂.1.1.1.2⟩, VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.1.1.2 h₂.1.1.2⟩,
    VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.1.2 h₂.1.2⟩, VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.2 h₂.2⟩

/-- The checks of two parts of writes, for both. -/
theorem K5Chk.append {p : Params} {STK nr : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr W₁)
    (h₂ : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr W₂) : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr (W₁ ++ W₂) :=
  ⟨VG.Proof.MlDsa.Arm.Verify.vcChk_append h₁.vc h₂.vc, VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.hint h₂.hint,
    fun r hr s hs => VG.Proof.MlDsa.Arm.Verify.sepAll_append (h₁.a r hr s hs) (h₂.a r hr s hs), fun i hi => VG.Proof.MlDsa.Arm.Verify.sepAll_append (h₁.z i hi) (h₂.z i hi),
    VG.Proof.MlDsa.Arm.Verify.sepAll_append h₁.c h₂.c, fun r hr => VG.Proof.MlDsa.Arm.Verify.sepAll_append (h₁.rows r hr) (h₂.rows r hr)⟩

/-! `K5Chk` of the writes of a part, from those of each region, each proved once for
any region (`k5chk` on a literal list of writes costs seconds). -/

theorem K5Chk.nil {p : Params} (_ : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK nr : Nat} (_ : nr ≤ p.k) : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr [] :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem K5Chk.stk {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr [(1, 0, STK)] := by
  k5chk hF

/-- A write to `scratch` apart from what `KC5` holds. -/
theorem K5Chk.c0 {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ 840 ∨ 876 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o) (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o)
    (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr [(0, o, n)] := by
  simp only [oB, oP] at h2 h3 h4 h5
  rcases hF.w1l with hw1 | ⟨hw1, _⟩ <;> rw [hw1] at h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk, hw1]

theorem K5Chk.cons_c0 {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    {W : List (Nat × Nat × Nat)}
    (h1 : o + n ≤ 840 ∨ 876 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o ∨ oB + 1024 ≤ o)
    (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o) (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) (h : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr W) :
    VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr ((0, o, n) :: W) := by
  have : w1Len p * nr ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega
  exact (K5Chk.c0 hF hnr h1 (by omega) h3 h4 h5).append (W₁ := [_]) h

theorem K5Chk.cons_stk {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {W : List (Nat × Nat × Nat)}
    (h : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr W) : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr ((1, 0, STK) :: W) :=
  (K5Chk.stk hF hnr).append (W₁ := [_]) h

/-- Proves a `K5Chk` of writes to `scratch` and the stack, with `hnr : nr ≤ p.k`. -/
macro "k5chks " hF:term:max hnr:term:max : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact VG.Proof.MlDsa.Arm.Verify.K5Chk.nil $hF $hnr
    | apply VG.Proof.MlDsa.Arm.Verify.K5Chk.cons_stk $hF $hnr
    | apply VG.Proof.MlDsa.Arm.Verify.K5Chk.cons_c0 $hF $hnr)
  all_goals (
    have := ($hF).w1.1; have := ($hF).k; have := ($hF).l
    try simp only [VG.Impl.MlDsa.Arm.Verify.oP, VG.Impl.MlDsa.Arm.Verify.oB, VG.Impl.MlDsa.Arm.Verify.oSS,
      VG.Impl.MlDsa.Arm.Verify.oCT]
    omega_arith)))

theorem KC5.keep {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ : State} {A' : Nat → Nat → Spec.MlDsa.Poly}
    {cc : Spec.MlDsa.Poly} {h : List (Vector Bool Spec.MlDsa.n)} {R : BitVec 32} {nz : Nat} {nc : Bool} {nr : Nat}
    {s s' : State} (hk5 : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R nz nc nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).RL W) s s') (hc : VG.Proof.MlDsa.Arm.Verify.K5Chk p STK nr W) : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R nz nc nr s' := by
  have hL := hk5.vc.site.ok
  have hle : w1Len p ≤ 2 ^ 64 := by rcases hF.w1l with e | ⟨e, _⟩ <;> omega
  exact ⟨hk5.vc.keep hk hc.vc, hk5.hh, VG.Proof.MlDsa.Arm.Verify.hintIs_keepW hL hk.frame hc.hint (by decide) (by have := hF.k; omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL hk.frame (hc.a r hr s' hs') (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL hk.frame (hc.z i hi) (by decide) rfl (hk5.z i hi),
    polyIs_keepW hL hk.frame hc.c (by decide) rfl hk5.c,
    fun r hr => by rw [bytes_keepW hL hk.frame (hc.rows r hr) (by decide) hle]; exact hk5.rows r hr,
    (hk.cs .r11 (by decide) (by decide)).trans hk5.r11, hk5.gd⟩

/-- The states of `compute` with `nz`, `nc` and `nr`, for some `A'`, `cc`, `h` and `R`. -/
abbrev KX (p : Params) (STK : Nat) (nz : Nat) (nc : Bool) (nr : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R nz nc nr s

/-! ## The NTTs of `z` and `c` -/

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem nttZ_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A' cc h R} {s : State}
    (hk5 : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R j false 0 s) : WP isa (nttAt P (pZ j)) s (VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R (j + 1) false 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  have hz := hk5.z j hj
  rw [ifn (Nat.lt_irrefl j)] at hz
  unfold nttAt
  refine ip_ok (t := VG.Spec.MlDsa.ntt) hP.ntt hs (by omega) (f := pZ j) (w := sc oSS) ⟨rfl, by vsep hF⟩ ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (by vsep hF) hz.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]), hk5.hh,
    VG.Proof.MlDsa.Arm.Verify.hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => ?_, polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl hk5.c,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r11 (by decide) (by decide)).trans hk5.r11, hk5.gd⟩
  by_cases e : i = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ i)) _
    have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ i)) = _ := hz.2
    rw [e2] at hb
    exact hb
  · have := polyIs_keepW hL k'.frame (i := 0) (o := oP (8 + i)) (by vsep hF) (by decide) rfl (hk5.z i hi)
    by_cases hlt : i < j
    · rwa [ifp hlt, ← ifp (show i < j + 1 by omega) (zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i) (toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i))] at this
    · rwa [ifn hlt, ← ifn (show ¬ i < j + 1 by omega) (zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i) (toRq (vZ p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) i))] at this

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK j false 0) (VG.Proof.MlDsa.Arm.Verify.KX p STK (j + 1) false 0) (nttAt P (pZ j)) := by
  have hl := hF.l
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (VG.Proof.MlDsa.Arm.Verify.nttZ_ok hP hF hS hj hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
    Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)))
    (RelCT.exists_ fun σ => ip_tr (t := VG.Spec.MlDsa.ntt) hP.ntt (by omega) (f := pZ j) (w := sc oSS)
      (⟨rfl, by vsep hF⟩ : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j) 1024) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
      (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (by vsep hF) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pZ j)) := (h₂.z j hj).1
  rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at r₂
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, (h₁.z j hj).1, r₂⟩

theorem nttC_ok {σ : State} {A' cc h R} {s : State} (hk5 : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ false 0 s) :
    WP isa (nttAt P VG.Impl.MlDsa.Arm.Verify.pC) s (VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ true 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  unfold nttAt
  refine ip_ok (t := VG.Spec.MlDsa.ntt) hP.ntt hs (by omega) (f := VG.Impl.MlDsa.Arm.Verify.pC) (w := sc oSS) ⟨rfl, by vsep hF⟩ ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (by vsep hF) hk5.c.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [VG.Proof.MlDsa.Arm.Verify.vcChk]), hk5.hh,
    VG.Proof.MlDsa.Arm.Verify.hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r11 (by decide) (by decide)).trans hk5.r11, hk5.gd⟩
  show PolyIs s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) _
  have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) = cc := hk5.c.2
  rw [e2] at hb
  exact hb

theorem nttC_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ false 0) (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true 0) (nttAt P VG.Impl.MlDsa.Arm.Verify.pC) := by
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (VG.Proof.MlDsa.Arm.Verify.nttC_ok hP hF hS hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
    Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC))
    (RelCT.exists_ fun σ => ip_tr (t := VG.Spec.MlDsa.ntt) hP.ntt (by omega) (f := VG.Impl.MlDsa.Arm.Verify.pC) (w := sc oSS)
      (⟨rfl, by vsep hF⟩ : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC 1024) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
      (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) (by vsep hF) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pC) := h₂.c.1
  rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at r₂
  exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, h₁.c.1, r₂⟩

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Row`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: the rows of `w′₁`

Row `r`: the sum of the products `Â[r, s] ẑ[s]` in `W` (polynomial 18),
`t̂₁[r]` unpacked from the public key (polynomial 16) and in the NTT domain,
`ĉ t̂₁[r]` (polynomial 17) subtracted from the sum, `NTT⁻¹` of it, `w′₁[r]`
(polynomial 19) by `UseHint`, and its `SimpleBitPack` to `B` (`row_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  mul_ok mul_tr mulAdd_ok mulAdd_tr sub_ok sub_tr MulOk AccOk T1Ok t1_ok t1_tr UhOk uh_ok uh_tr SbpOk sbp_ok sbp_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (seqR)
open VG.Spec.MlDsa (Params HintIs PolyIs NatPolyIs toRq polyAt natPolyAt coeffAt Reduced ntt nttInv multiplyNTT sub
  simpleBitPack useHint ofInt simpleBitUnpack t1Max d n q)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row wRow dotAcc t1Hat vT1)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `j` of the working space is `f`. -/
abbrev PIs (p : Params) (STK : Nat) (σ : State) (j : Nat) (f : Spec.MlDsa.Poly) (s : State) : Prop :=
  PolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP j)) f

/-- In row `r`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (r : Nat)
    (f : State → (Nat → Nat → Spec.MlDsa.Poly) → Spec.MlDsa.Poly → List (Vector Bool n) → State → Prop)
    (σ s : State) : Prop :=
  ∃ A' cc h R, VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ true r s ∧ f σ A' cc h s

/-- `t₁[r]` unpacked. -/
abbrev t1Raw (pk : List Byte) (r : Nat) : Spec.MlDsa.Poly := (vT1 pk r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem KC5.aR {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc nr} {s : State}
    (hk : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R nz nc nr s) {r j : Nat} (hr : r < p.k) (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.PIs p STK σ (20 + 8 * r + j) (A' r j) s := hk.a r hr j hj

theorem KC5.zR {p : Params} {STK : Nat} {σ : State} {A' cc h R nc nr} {s : State}
    (hk : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ nc nr s) {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.PIs p STK σ (8 + j) (zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) j) s := by
  have := hk.z j hj; rwa [ifp hj] at this

theorem KC5.cR {p : Params} {STK : Nat} {σ : State} {A' cc h R nr} {s : State}
    (hk : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ true nr s) : VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 15 (VG.Spec.MlDsa.ntt cc) s := by
  have := hk.c; rwa [ifp rfl] at this

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
  {r : Nat} (hr : r < p.k)
include hP hF hS hr

/-! ## `W = Σₛ Â[r, s] ẑ[s]` -/

omit hP hS in
theorem mulW_m {σ : State} {j : Nat} (hj : j < p.ℓ) : MulOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb VG.Impl.MlDsa.Arm.Verify.pW (pA r j) (pZ j) := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulW_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true r) (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r 1))
      (mulAt P VG.Impl.MlDsa.Arm.Verify.pW (pA r 0) (pZ 0)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr (j := 0) (by omega)
    have hz := hk5.zR (j := 0) (by omega)
    refine mul_ok hP.mul hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.mulW_m hF hr (by omega)) ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    show PolyIs s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) _
    rw [show dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r 1 = _ from Proof.MlDsa.Verify.add_zero_left _]
    have e1 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r 0)) = A' r 0 := ha.2
    have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ 0)) = zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) 0 := hz.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      (Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r 0)) ∧ Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ 0))) ∧
      (Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r 0)) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ 0))))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega) (VG.Proof.MlDsa.Arm.Verify.mulW_m hF (σ := σ) hr (by omega))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
    have a₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pA r 0)) := (h₂.aR hr (j := 0) (by omega)).1
    have z₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pZ 0)) := (h₂.zR (j := 0) (by omega)).1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at a₂ z₂
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, ⟨(h₁.aR hr (j := 0) (by omega)).1, (h₁.zR (j := 0) (by omega)).1⟩, ⟨a₂, z₂⟩⟩

theorem mulAddW_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r j))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r (j + 1)))
      (mulAddAt P VG.Impl.MlDsa.Arm.Verify.pW (pA r j) (pZ j)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr hj
    have hz := hk5.zR hj
    refine mulAdd_ok hP.mulAdd hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.mulW_m hF hr hj) hw.1 ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    show PolyIs s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) _
    have e0 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) = dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r j := hw.2
    have e1 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r j)) = A' r j := ha.2
    have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j)) = zHat p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) j := hz.2
    rw [e0, e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      (Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r j)) ∧
        Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j))) ∧
      (Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pA r j)) ∧
        Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (pZ j))))
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd (by omega) (VG.Proof.MlDsa.Arm.Verify.mulW_m hF (σ := σ) hr hj)
        fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pW) := w₂.1
    have a₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pA r j)) := (h₂.aR hr hj).1
    have z₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) (pZ j)) := (h₂.zR hj).1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at w₂' a₂ z₂
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, (h₁.aR hr hj).1, (h₁.zR hj).1⟩, ⟨w₂', a₂, z₂⟩⟩

theorem dot_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true r) (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ))
      (dot P p r) := by
  have hl := hF.l
  unfold dot
  refine (VG.Proof.MlDsa.Arm.Verify.mulW_piece hP hF hS hr).seq (Piece.mono (Piece.seqR
    (I := fun j => VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r j)) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.Arm.Verify.mulAddW_piece hP hF hS hr (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_)
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## `t̂₁[r]` -/

/-- After `t₁[r]`. -/
abbrev F2 (p : Params) (STK r : Nat) (t : State → Spec.MlDsa.Poly) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly)
    (_cc : Spec.MlDsa.Poly) (_h : List (Vector Bool n)) (s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ) s ∧ VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 16 (t σ) s

omit hP hS in
theorem t1_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.T1Ok (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (.r4, 32 + 320 * r) pT := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF⟩

theorem t1_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' _ _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F2 p STK r fun σ => VG.Proof.MlDsa.Arm.Verify.t1Raw (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r)) (unpackT1At P (.r4, 32 + 320 * r) pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold unpackT1At
    refine VG.Proof.MlDsa.Arm.KeyGen.t1_ok hP.unpackT1 hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.t1_m hF hr) fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r4, 32 + 320 * r)) 320 =
        ((VG.Proof.MlDsa.Arm.Verify.pkOf p σ).drop (32 + 320 * r)).take 320 := VG.Proof.MlDsa.Arm.Verify.pk_slice hk5.vc (by rw [hF.pk]; omega)
    rw [e] at hb
    exact hb
  · unfold unpackT1At
    exact rel_of (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.t1_tr hP.unpackT1 (by omega) (VG.Proof.MlDsa.Arm.Verify.t1_m hF (σ := σ) hr) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc⟩

omit hP hS hr in
theorem nttT_m {σ : State} : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT 1024 ∧ PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc oSS) 1024 ∧
    sepB (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).sizes (tri pT 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, by vsep hF⟩

theorem nttT_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F2 p STK r fun σ => VG.Proof.MlDsa.Arm.Verify.t1Raw (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F2 p STK r fun σ => t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r)) (nttAt P pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.Verify.nttT_m hF (STK := STK) (σ := σ)
    unfold nttAt
    refine ip_ok (t := VG.Spec.MlDsa.ntt) hP.ntt hk5.vc.site (by omega) m1 m2 (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
      (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) m3 ht.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT) = VG.Proof.MlDsa.Arm.Verify.t1Raw (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r := ht.2
    rw [e] at hb
    exact hb
  · unfold nttAt
    refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.Verify.nttT_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := VG.Spec.MlDsa.ntt) hP.ntt (by omega) m1 m2 (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
          (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have t₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) pT) := t₂.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at t₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, t₁.1, t₂'⟩

/-! ## `W = NTT⁻¹(W - ĉ t̂₁[r])` -/

/-- After `ĉ t̂₁[r]`. -/
abbrev F4 (p : Params) (STK r : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (_h : List (Vector Bool n)) (s : State) : Prop :=
  VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ) s ∧ VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 17 (multiplyNTT (VG.Spec.MlDsa.ntt cc) (t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r)) s

omit hP hS hr in
theorem mulT_m {σ : State} : MulOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb pT2 VG.Impl.MlDsa.Arm.Verify.pC pT := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulT_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F2 p STK r fun σ => t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r)) (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F4 p STK r))
      (mulAt P pT2 VG.Impl.MlDsa.Arm.Verify.pC pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · have hc := hk5.cR
    refine mul_ok hP.mul hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.mulT_m hF) hc.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e1 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) = VG.Spec.MlDsa.ntt cc := hc.2
    have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT) = t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      (Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) ∧ Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT)) ∧
      (Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pC) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT)))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega) (VG.Proof.MlDsa.Arm.Verify.mulT_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have c₂ : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pC) := h₂.cR.1
    have t₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) pT) := t₂.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at c₂ t₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, ⟨h₁.cR.1, t₁.1⟩, ⟨c₂, t₂'⟩⟩

omit hP hS hr in
theorem subW_m {σ : State} : AccOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb VG.Impl.MlDsa.Arm.Verify.pW pT2 := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF⟩

theorem subW_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r (VG.Proof.MlDsa.Arm.Verify.F4 p STK r))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18
        (VG.Spec.MlDsa.sub (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ) (multiplyNTT (VG.Spec.MlDsa.ntt cc) (t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r))))
      (subAt P VG.Impl.MlDsa.Arm.Verify.pW pT2) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · refine sub_ok hP.sub hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.subW_m hF) hw.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e1 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) = dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ := hw.2
    have e2 : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT2) = _ := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      (Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT2)) ∧
      (Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pT2)))
      (RelCT.exists_ fun σ => sub_tr hP.sub (by omega) (VG.Proof.MlDsa.Arm.Verify.subW_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁, t₁⟩ ⟨_, _, _, _, h₂, w₂, t₂⟩ => ?_
    have w₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pW) := w₂.1
    have t₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) pT2) := t₂.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at w₂' t₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, t₁.1⟩, ⟨w₂', t₂'⟩⟩

omit hP hS hr in
theorem invW_m {σ : State} : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW 1024 ∧ PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc oSS) 1024 ∧
    sepB (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).sizes (tri VG.Impl.MlDsa.Arm.Verify.pW 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, by vsep hF⟩

theorem invW_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18
        (VG.Spec.MlDsa.sub (dotAcc p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' r p.ℓ) (multiplyNTT (VG.Spec.MlDsa.ntt cc) (t1Hat (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r))))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (wRow p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) r))
      (invNttAt P VG.Impl.MlDsa.Arm.Verify.pW) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.Verify.invW_m hF (STK := STK) (σ := σ)
    unfold invNttAt
    refine ip_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt hk5.vc.site (by omega) m1 m2 (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
      (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) m3 hw.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) = _ := hw.2
    rw [e] at hb
    exact hb
  · unfold invNttAt
    refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := VG.Proof.MlDsa.Arm.Verify.invW_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt (by omega) m1 m2 (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide)
          (show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pW) := w₂.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at w₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

/-! ## `w′₁[r]`, packed to `B` -/

omit hP hS in
theorem uh_m {σ : State} : VG.Proof.MlDsa.Arm.KeyGen.UhOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb (VG.Impl.MlDsa.Arm.Verify.pH r) VG.Impl.MlDsa.Arm.Verify.pW p.γ₂ pW1 := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF,
    by vsep hF, hF.g2.1, hF.g2.2⟩

omit hP hF hS in
theorem hint_row {σ : State} {m : Mem} {h : List (Vector Bool n)}
    (hh : HintIs m ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0)) p.k h) :
    (Spec.MlDsa.hintAt m (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (VG.Impl.MlDsa.Arm.Verify.pH r)) 1).headD (Vector.replicate n false) =
      h.getD r (Vector.replicate n false) := by
  have e : lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (VG.Impl.MlDsa.Arm.Verify.pH r) = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 0) + BitVec.ofNat 64 (1024 * r) := by
    show (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP r) = _
    rw [Lay.A, Lay.A, add_ofNat_add, show oP 0 + 1024 * r = oP r by simp only [oP]]
  rw [e]
  exact Proof.MlDsa.Verify.hintAt_row hh hr

theorem uh_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc _ => VG.Proof.MlDsa.Arm.Verify.PIs p STK σ 18 (wRow p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) r))
      (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 19))
        (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) h r))
      (useHintAt P (VG.Impl.MlDsa.Arm.Verify.pH r) VG.Impl.MlDsa.Arm.Verify.pW p.γ₂ pW1) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold useHintAt
    refine VG.Proof.MlDsa.Arm.KeyGen.uh_ok hP.useHint hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.uh_m hF hr) hw.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e : polyAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) = _ := hw.2
    rw [e, VG.Proof.MlDsa.Arm.Verify.hint_row hr hk5.hint] at hb
    exact hb
  · unfold useHintAt
    refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      Reduced x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW) ∧ Reduced y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Impl.MlDsa.Arm.Verify.pW))
      (RelCT.exists_ fun σ => VG.Proof.MlDsa.Arm.KeyGen.uh_tr hP.useHint (by omega) (VG.Proof.MlDsa.Arm.Verify.uh_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) VG.Impl.MlDsa.Arm.Verify.pW) := w₂.1
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at w₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

omit hP hS in
theorem sbpW_m {σ : State} : SbpOk (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p) := by
  have hk := hF.k
  rcases hF.w1l with e | ⟨e, _⟩ <;>
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF [e]⟩, show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide, by vsep hF [e],
    hF.sbp.1, hF.sbp.2.1⟩

omit hP hS hr in
theorem w1_bound {σ : State} {m : Mem} {a : Addr} {A' : Nat → Nat → Spec.MlDsa.Poly} {ch : Spec.MlDsa.Poly}
    {h : List (Vector Bool n)} {r : Nat} (h1 : NatPolyIs m a (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' ch h r)) :
    ∀ i < n, (coeffAt m a i).toNat ≤ w1Max p := fun i hi => by
  rw [show (coeffAt m a i).toNat = (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' ch h r)[i]'hi from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [w1Row, Vector.getElem_zipWith]
  exact Proof.MlDsa.Verify.useHint_le hF.g2.1 _ _

theorem sbpW_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 19))
        (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) h r))
      (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true (r + 1)) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold sbpAt
    refine sbp_ok hP.simpleBitPack hk5.vc.site (by omega) (VG.Proof.MlDsa.Arm.Verify.sbpW_m hF hr) (VG.Proof.MlDsa.Arm.Verify.w1_bound hF hw) fun s' k' hb =>
      ⟨A', cc, h, R, ?_⟩
    have hk' := hk5.keep hF k' (by
      have : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
        rw [← Nat.mul_succ, Nat.mul_comm p.k]; exact Nat.mul_le_mul_left _ hr
      k5chks hF (Nat.le_of_lt hr))
    refine ⟨hk'.vc, hk'.hh, hk'.hint, hk'.a, hk'.z, hk'.c, fun r' hr' => ?_, hk'.r11, hk'.gd⟩
    rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
    · exact hk'.rows r' hr'
    · show bytesAt s'.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc (oB + w1Len p * r'))) (w1Len p) = _
      rw [hb]
      exact congrArg (VG.Spec.MlDsa.simpleBitPack · (w1Max p)) hw
  · unfold sbpAt
    refine rel_of (Q := fun x y => ∃ σ, VG.Proof.MlDsa.Arm.KeyGen.Two (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK x y ∧
      (∀ i < n, (coeffAt x.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pW1) i).toNat ≤ w1Max p) ∧
      (∀ i < n, (coeffAt y.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) pW1) i).toNat ≤ w1Max p))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack (by omega) (VG.Proof.MlDsa.Arm.Verify.sbpW_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : ∀ i < n, (coeffAt _ (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK _) pW1) i).toNat ≤ w1Max p := VG.Proof.MlDsa.Arm.Verify.w1_bound hF w₂
    rw [← VG.Proof.MlDsa.Arm.Verify.vlay_pub pub] at w₂'
    exact ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc, VG.Proof.MlDsa.Arm.Verify.w1_bound hF w₁, w₂'⟩

theorem row_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true r) (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true (r + 1)) (row P p r) :=
  (VG.Proof.MlDsa.Arm.Verify.dot_piece hP hF hS hr).seq ((VG.Proof.MlDsa.Arm.Verify.t1_piece hP hF hS hr).seq ((VG.Proof.MlDsa.Arm.Verify.nttT_piece hP hF hS hr).seq
    ((VG.Proof.MlDsa.Arm.Verify.mulT_piece hP hF hS hr).seq ((VG.Proof.MlDsa.Arm.Verify.subW_piece hP hF hS hr).seq ((VG.Proof.MlDsa.Arm.Verify.invW_piece hP hF hS hr).seq
      ((VG.Proof.MlDsa.Arm.Verify.uh_piece hP hF hS hr).seq (VG.Proof.MlDsa.Arm.Verify.sbpW_piece hP hF hS hr)))))))

end

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Hash`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)`

Once every row of `w′₁` is packed to `B`, the commitment hash of `μ` and `B`,
to `CT` (`vhash_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv hashLay hashLay_ptr
  hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlKem.Arm (hash)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt Reduced ntt simpleBitPack)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → VG.Proof.MlDsa.Arm.Verify.Kmu i = true → VG.Proof.MlDsa.Arm.Verify.Kmu j = true → i ∈ VG.Proof.MlDsa.Arm.Verify.vWb ∨ j ∈ VG.Proof.MlDsa.Arm.Verify.vWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [VG.Proof.MlDsa.Arm.Verify.Kmu, beq_iff_eq] at hi hj; omega

/-- `w1Encode(w′₁)` of rows `A'`, `cc` and `h`. -/
abbrev w1Enc (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) : List Byte :=
  (List.range p.k).flatMap fun r => VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (VG.Spec.MlDsa.ntt cc) h r) (w1Max p)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.Arm.Verify.flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- After the hash. -/
abbrev KF (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ true p.k s ∧
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oCT) p.ctildeLen = Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Verify.muOf σ ++ VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc h) p.ctildeLen

theorem vhPieces {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ s : State} (hs : Site (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) VG.Proof.MlDsa.Arm.Verify.vWb STK s) :
    (∀ pc ∈ ([⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) s VG.Proof.MlDsa.Arm.Verify.Kmu) ix s false pc) ∧
    PieceOk (hashLay (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) s VG.Proof.MlDsa.Arm.Verify.Kmu) ix s true (⟨.r7, oCT, p.ctildeLen⟩ : Impl.MlKem.Arm.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b, w1c⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show encodable (BitVec.ofNat 32 oCT) = true by decide)
    (show encodable (BitVec.ofNat 32 p.ctildeLen) = true by rcases hF.ct with e | e | e <;> rw [e] <;> decide)
    (show 0 < p.ctildeLen by rcases hF.ct with e | e | e <;> omega)
    (show oCT + p.ctildeLen < 2 ^ 32 by simp only [oCT]; rcases hF.ct with e | e | e <;> omega)
    (by rcases hF.ct with e | e | e <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.r7 ∈ VG.Proof.MlDsa.Arm.Verify.vWb by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide)
      (show encodable (BitVec.ofNat 32 64) = true by decide) (by decide) (by decide)
      (by vsep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show encodable (BitVec.ofNat 32 oB) = true by decide) w1c w1b (by simp only [oB]; omega)
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

theorem B_bytes {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc} {s : State}
    (hk5 : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R nz nc p.k s) :
    bytesAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oB) (p.k * w1Len p) = VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc h := by
  rw [Nat.mul_comm, Lay.A, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ oB (w1Len p) p.k]
  exact VG.Proof.MlDsa.Arm.Verify.flatMap_congr_mem' fun r hr => hk5.rows r (List.mem_range.mp hr)

theorem vhash_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ : State} {A' cc h R} {s : State}
    (hk5 : VG.Proof.MlDsa.Arm.Verify.KC5 p STK σ A' cc h R p.ℓ true p.k s) :
    WP isa (hash 136 0x1f [⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] [⟨.r7, oCT, p.ctildeLen⟩]) s (VG.Proof.MlDsa.Arm.Verify.KF p STK σ) := by
  have hk := hF.k
  have hs := hk5.vc.site
  obtain ⟨hin, hq⟩ := VG.Proof.MlDsa.Arm.Verify.vhPieces hF hs
  refine WP.mono (hashS hs VG.Proof.MlDsa.Arm.Verify.kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨A', cc, h, R, hk5.keep hF k' ?_, ?_⟩
  · have : p.ctildeLen ≤ 64 := by rcases hF.ct with e | e | e <;> omega
    k5chks hF (Nat.le_refl _)
  · have o₃ : bytesAt s'.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 oCT) p.ctildeLen = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).ptr (ix Reg.r5)) + BitVec.ofNat 64 0) 64 = VG.Proof.MlDsa.Arm.Verify.muOf σ :=
      hk5.vc.mu
    have e2 : bytesAt s.mem (State.addr ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).ptr (ix Reg.r7)) + BitVec.ofNat 64 oB) (p.k * w1Len p) =
        VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc h := VG.Proof.MlDsa.Arm.Verify.B_bytes hk5
    rw [e1, e2, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem vhash_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true p.k) (VG.Proof.MlDsa.Arm.Verify.KF p STK)
      (hash 136 0x1f [⟨.r5, 0, 64⟩, ⟨.r7, oB, p.k * w1Len p⟩] [⟨.r7, oCT, p.ctildeLen⟩]) :=
  ⟨fun _ _ _ ⟨_, _, _, _, h⟩ => VG.Proof.MlDsa.Arm.Verify.vhash_ok hF h,
    rel_of (RelCT.exists_ fun σ => hashS_tr VG.Proof.MlDsa.Arm.Verify.kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide)
      (by simp) (fun s hs => (VG.Proof.MlDsa.Arm.Verify.vhPieces hF (σ := σ) hs).1) (fun s hs => (VG.Proof.MlDsa.Arm.Verify.vhPieces hF hs).2) fun _ _ h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Cmp`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: `c̃′ = c̃`

`cmpAnd` ORs the XORs of the bytes of `c̃′` and `c̃` into `r12` (ML-KEM's
`cmp_step`), and ANDs `r11` with 1 exactly when that is 0 (`cmpAnd_ok`),
without a branch.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk base_pres ldc_eq)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (Ptr Arg ldc)
open VG.Impl.MlKem.Arm (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (h4 : s'.gpr .r4 = s.gpr .r4) (h5 : s'.gpr .r5 = s.gpr .r5) (h6 : s'.gpr .r6 = s.gpr .r6)
    (h7 : s'.gpr .r7 = s.gpr .r7) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s8, by rw [hsp]; exact h.spk,
    by rw [h7]; exact h.r7, by rw [h4]; exact h.r4, by rw [h5]; exact h.r5, by rw [h6]; exact h.r6,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s)
    (hr : ∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s' :=
  ⟨VG.Proof.MlDsa.Arm.Verify.siteCongr h.site (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)) (hr _ (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.lr, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu,
    by rw [hm]; exact h.sg⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) (n : Nat) (s : State) :
    WP isa (.block (Arg.instrs .r0 (.ptr a) ++ Arg.instrs .r1 (.ptr b) ++ ldc .r9 n ++
      ([.mov .r12 (.imm 0)] : List Instr))) s fun s' =>
      s'.gpr .r0 = s.gpr a.1 + BitVec.ofNat 32 a.2 ∧ s'.gpr .r1 = s.gpr b.1 + BitVec.ofNat 32 b.2 ∧
      s'.gpr .r9 = BitVec.ofNat 32 n ∧ s'.gpr .r12 = 0 ∧ (∀ r ∈ preserved, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨na0, -, -, -, -⟩ := pres_ne (base_pres (r := a.1) (by simpa [argOk] using ha)).1
    (base_pres (r := a.1) (by simpa [argOk] using ha)).2
  obtain ⟨nb0, nb1, -, -, -⟩ := pres_ne (base_pres (r := b.1) (by simpa [argOk] using hb)).1
    (base_pres (r := b.1) (by simpa [argOk] using hb)).2
  apply WP.of_runBlock
  simp (config := { decide := true }) only [Arg.instrs, ldc, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some, Option.some.injEq,
    exists_eq_left', gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, na0,
    nb0, nb1, ldc_eq, ↓reduceIte, true_and, and_true]
  intro r hr h9
  have : ¬ r = .r0 ∧ ¬ r = .r1 ∧ ¬ r = .r12 := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [this, h9, ↓reduceIte]

theorem shr31_eq : ∀ n < 256, (BitVec.ofNat 32 n - 1) >>> 31 = if n = 0 then (1 : BitVec 32) else 0 := by
  decide +kernel

theorem shr31_of {v : BitVec 32} (h : v.toNat < 256) : (v - 1) >>> 31 = if v = 0 then (1 : BitVec 32) else 0 := by
  have := VG.Proof.MlDsa.Arm.Verify.shr31_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [this]
  by_cases e : v = 0
  · rw [e]; rfl
  · rw [ite_eq_right (fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))), ite_eq_right e]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.dp .sub .r12 .r12 (.imm 1), .mov .r12 (.shifted .r12 .lsr 31), .dp .and .r11 .r11 (.reg .r12)]) s
      fun s' => s'.gpr .r11 = s.gpr .r11 &&& ((s.gpr .r12 - 1) >>> 31) ∧
        (∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    Option.map_some, Option.some.injEq, exists_eq_left', gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg,
    ↓reduceIte, and_true, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true]

/-- `r11 ← r11 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 32) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 &&& VG.Proof.MlDsa.Arm.Verify.flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ [Reg.r4, .r5, .r6, .r7], s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  have fS := hs.fitE pa hn
  have fD := hs.fitE pb hn
  have cr : Covers [⟨State.addr (L.ptr (ix a.1) + BitVec.ofNat 32 a.2), n⟩,
      ⟨State.addr (L.ptr (ix b.1) + BitVec.ofNat 32 b.2), n⟩] (s.rd ++ s.wr) := by
    rw [hs.addrE pa hn, hs.addrE pb hn]
    exact Sample.covers_cons (hs.crE pa) (Sample.covers_cons (hs.crE pb) Sample.covers_nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Verify.cmpPre_ok pa.1 pb.1 n s) fun s₁ ⟨g0, g1, g9, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (r := a.1) (by simpa [argOk] using pa.1)] at g0
  rw [hs.base (r := b.1) (by simpa [argOk] using pb.1)] at g1
  refine WP.seq (wp_loop_ne (CmpInv (L.ptr (ix a.1) + BitVec.ofNat 32 a.2) (L.ptr (ix b.1) + BitVec.ofNat 32 b.2)
      n s₁) (N := n) hn (fun k hk s h => cmp_step fS fD hn' (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g0]; simp, by rw [g1]; simp, by rw [g9]; simp, fun _ _ _ => rfl, rfl, rfl, rfl, rfl,
      by rw [g12]; decide, by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (VG.Proof.MlDsa.Arm.Verify.cmpPost_ok s₂) fun s' ⟨r11, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e11 : s₂.gpr .r11 = s.gpr .r11 :=
      (h.cs .r11 (by decide) (by decide)).trans (cs .r11 (by decide) (by decide))
    rw [r11, VG.Proof.MlDsa.Arm.Verify.shr31_of h.lt, e11]
    congr 1
    have key : s₂.gpr .r12 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m, ← hs.addrE pa hn, ← hs.addrE pb hn]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .r12 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, VG.Proof.MlDsa.Arm.Verify.flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, VG.Proof.MlDsa.Arm.Verify.flag, Bool.false_eq_true]
  · rw [rs r hr]
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h9 : r ≠ .r9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    exact (h.cs r hp h9).trans (cs r hp h9)

/-! ## After the comparison -/

/-- At the end of `compute`: `r11` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ VG.Proof.MlDsa.Arm.Verify.hintOf p σ = some h ∧ h.length = p.k ∧ VG.Proof.MlDsa.Arm.Verify.Gd p σ A' cc R ∧
    s.gpr .r11 = R &&& VG.Proof.MlDsa.Arm.Verify.flag (decide (Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Verify.muOf σ ++ VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.r6, 0) p.ctildeLen) s (VG.Proof.MlDsa.Arm.Verify.KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨rfl, ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, 0) p.ctildeLen := by
    refine ⟨rfl, ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (VG.Proof.MlDsa.Arm.Verify.cmpAnd_okS hk5.vc.site pa pb (by omega) (by omega))
    fun s' ⟨r11, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (.r6, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) := by
    have := VG.Proof.MlDsa.Arm.Verify.sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r11, e0, e4, hk5.r11]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.Arm.taint.check
    (Taint.ofRegs [.r4, .r5, .r6, .r7]) (cmpAnd (sc oCT) (.r6, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KF p STK) (VG.Proof.MlDsa.Arm.Verify.KE p STK) (cmpAnd (sc oCT) (.r6, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.cmp_ok hF h, rel_of (VG.Proof.MlDsa.Arm.Verify.vtaint4 (VG.Proof.MlDsa.Arm.Verify.cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, VG.Proof.MlDsa.Arm.Verify.vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top`. -/
section

/-!
# ML-DSA verification on 32-bit ARM: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

After the samplers, the NTTs, the rows, the hash and the comparison
(`compute_piece`); what `r11` then says of `verifyMu` (`ke_out`); and the
whole body, piece by piece, for any parameter set of Table 1 and any verified
implementations of the primitives (`body_piece`): a malformed hint gives 0 at
once, a `z` too large 0 after the norms, and otherwise `r11` is the samplers'
result and the comparison of `c̃`.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart hashLay hashLay_ptr)
open VG.Impl.MlKem.Arm (topEnd)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (seqR)
open VG.Spec.MlDsa (Params Bounds verifyMu minBounds toRq polyAt rejNTTPoly sampleInBall)
open VG.Proof.MlDsa.Verify (vZ vCt vHint aSeed common_bound verifyMu_rows verifyMu_norm verifyMu_hint_none
  verifyMu_rej_none verifyMu_ball_none verifyMu_mono bmax_left bmax_right normR_vZ_iff)
open VG.Proof.MlDsa.KeyGen (ifn)
open VG.Spec.Sha3 (bytesAt)

/-- A piece keeps a fact about the entry state. -/
theorem pieceFrame {Pre : State → Prop} {Pub : State → State → Prop} {I J : State → State → Prop} {c : Prog isa}
    (h : Piece Pre Pub I J c) (F : State → Prop) :
    Piece Pre Pub (fun σ s => I σ s ∧ F σ) (fun σ s => J σ s ∧ F σ) c :=
  ⟨fun σ s hp ⟨hs, hf⟩ => WP.mono (h.ok σ s hp hs) fun _ h' => ⟨h', hf⟩,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h⟩

/-! ## The flags -/

theorem VC.flags {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VC p STK σ s) (a b : BitVec 32) :
    VG.Proof.MlDsa.Arm.Verify.VC p STK σ (subFlags s a b) :=
  h.congr (fun _ _ => rfl) rfl rfl rfl rfl

theorem V1.flags {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.V1 p STK σ s) {a b : BitVec 32} :
    VG.Proof.MlDsa.Arm.Verify.V1 p STK σ (subFlags s a b) :=
  ⟨h.vc.flags a b, h.r11, h.hint⟩

theorem V2.flags {p : Params} {STK j : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.V2 p STK j σ s) {a b : BitVec 32} :
    VG.Proof.MlDsa.Arm.Verify.V2 p STK j σ (subFlags s a b) :=
  ⟨h.vc.flags a b, h.hint, h.z, h.r11⟩

/-! ## After the samplers -/

theorem vs4_kx {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VS4 p STK σ s) : VG.Proof.MlDsa.Arm.Verify.KX p STK 0 false 0 σ s := by
  obtain ⟨hh, e, hi⟩ := h.vb.hint
  exact ⟨fun r c => polyAt s.mem (VG.Proof.MlDsa.Arm.Verify.aA p STK σ r c), polyAt s.mem ((VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 (oP 15)), hh, s.gpr .r11,
    h.vb.vc, e, hi, fun r hr c hc => ⟨h.red r hr c hc, rfl⟩,
    fun i hi => by rw [ifn (Nat.not_lt_zero i)]; exact h.vb.z i hi, ⟨h.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, h.ok⟩

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem compute_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.KX p STK 0 false 0) (VG.Proof.MlDsa.Arm.Verify.KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ false 0) ?_ ((VG.Proof.MlDsa.Arm.Verify.nttC_piece hP hF hS).seq
    (Piece.seq (J := VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true p.k) ?_ ((VG.Proof.MlDsa.Arm.Verify.vhash_piece hF).seq (VG.Proof.MlDsa.Arm.Verify.cmp_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.Arm.Verify.KX p STK j false 0) p.ℓ 0
      fun j _ hj => VG.Proof.MlDsa.Arm.Verify.nttZ_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun r => VG.Proof.MlDsa.Arm.Verify.KX p STK p.ℓ true r) p.k 0
      fun r _ hr => VG.Proof.MlDsa.Arm.Verify.row_piece hP hF hS (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

end

/-! ## The result -/

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.muOf σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)

/-- What the result `r` says of `verifyMu`, as `verifyContract` does. -/
abbrev VOut (p : Params) (σ : State) (r : BitVec 32) : Prop :=
  (r = 1 ∧ ∃ b, VG.Proof.MlDsa.Arm.Verify.vv p σ b = some true) ∨ (r = 0 ∧ VG.Proof.MlDsa.Arm.Verify.vv p σ minBounds ≠ some true)

/-- At the end, before the epilogue: the result in `r11`. -/
abbrev VFin (p : Params) (STK : Nat) (σ s : State) : Prop := VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ VG.Proof.MlDsa.Arm.Verify.VOut p σ (s.gpr .r11)

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : VG.Proof.MlDsa.Arm.Verify.vv p σ b = some false) : VG.Proof.MlDsa.Arm.Verify.vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

theorem ke_out {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.KE p STK σ s)
    (hz : VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ = true) : VG.Proof.MlDsa.Arm.Verify.VFin p STK σ s := by
  obtain ⟨A', cc, hh, R, vc, e, hl, ⟨q, hR, hok, hbad⟩, r11⟩ := h
  refine ⟨vc, ?_⟩
  rw [r11, hR, VG.Proof.MlDsa.Arm.Verify.flag_and]
  cases q with
  | false =>
    refine .inr ⟨rfl, ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ e hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ e hn']; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ, rejNTTPoly n (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r c) = some (A' r c))
      (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) r c) = some (A' r c))
          (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc => hA r hr c hc
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨c, hc, hc'⟩ := Option.map_eq_some_iff.mp hbB
    have ev := verifyMu_rows p ⟨0, 0, nA, bB⟩ (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.muOf σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) e hl hnA hc
    have ew : ((List.range p.k).flatMap fun r => Spec.MlDsa.simpleBitPack
        (Proof.MlDsa.Verify.w1Row p (VG.Proof.MlDsa.Arm.Verify.pkOf p σ) (VG.Proof.MlDsa.Arm.Verify.sgOf p σ) A' (Spec.MlDsa.ntt cc) hh r)
        ((Spec.MlDsa.q - 1) / (2 * p.γ₂) - 1)) = VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc hh := rfl
    rw [decide_eq_true ((normR_vZ_iff hF.nb.2 p hF.g1 _).mpr (of_decide_eq_true hz)), hc', Bool.true_and, ew] at ev
    by_cases hE : Spec.MlDsa.H (VG.Proof.MlDsa.Arm.Verify.muOf σ ++ VG.Proof.MlDsa.Arm.Verify.w1Enc p σ A' cc hh) p.ctildeLen = vCt p (VG.Proof.MlDsa.Arm.Verify.sgOf p σ)
    · exact .inl ⟨by rw [decide_eq_true hE]; rfl, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [decide_eq_false hE]; rfl,
        VG.Proof.MlDsa.Arm.Verify.false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem flag_ne {b : Bool} (h : VG.Proof.MlDsa.Arm.Verify.flag b ≠ 0) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem flag_eq {b : Bool} (h : VG.Proof.MlDsa.Arm.Verify.flag b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## The body -/

section
variable {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-- The samplers and the rest, once `z` is small enough. -/
theorem inner_piece :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.V2 p STK p.ℓ) (VG.Proof.MlDsa.Arm.Verify.VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine VG.Proof.MlDsa.Arm.Verify.ifOk_piece (v := fun σ => VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ)) (fun _ _ _ h => h.r11) (fun σ₁ σ₂ _ _ pub => ?_)
    (fun _ _ _ _ h => h.flags) ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.r11.trans hv, ?_⟩⟩
  · have e : VG.Proof.MlDsa.Arm.Verify.sgOf p σ₁ = VG.Proof.MlDsa.Arm.Verify.sgOf p σ₂ := pub.2.2.2.2.2.2.2
    dsimp only [VG.Proof.MlDsa.Arm.Verify.zOk]
    rw [e]
  · refine Piece.mono (VG.Proof.MlDsa.Arm.Verify.pieceFrame ((VG.Proof.MlDsa.Arm.Verify.samples_piece hP hF hS).seq (Piece.mono (VG.Proof.MlDsa.Arm.Verify.compute_piece hP hF hS)
      (fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.vs4_kx h) fun _ _ _ h => h)) fun σ => VG.Proof.MlDsa.Arm.Verify.zOk p σ p.ℓ = true)
      (fun _ _ _ h => ⟨h, VG.Proof.MlDsa.Arm.Verify.flag_ne h.2⟩) fun _ _ _ ⟨h, hz⟩ => VG.Proof.MlDsa.Arm.Verify.ke_out hF h hz
  · obtain ⟨hh, e, -⟩ := h.hint
    refine verifyMu_norm minBounds _ _ e fun hn => ?_
    have := VG.Proof.MlDsa.Arm.Verify.flag_eq hv
    rw [VG.Proof.MlDsa.Arm.Verify.zOk, decide_eq_false_iff_not] at this
    exact this ((normR_vZ_iff hF.nb.2 p hF.g1 _).mp hn)

omit hP hF hS in
theorem v1_v2 {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.V1 p STK σ s) (hv : VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.hintOf p σ).isSome ≠ 0) : VG.Proof.MlDsa.Arm.Verify.V2 p STK 0 σ s := by
  cases e : VG.Proof.MlDsa.Arm.Verify.hintOf p σ with
  | none => rw [e] at hv; exact absurd rfl hv
  | some hh =>
    refine ⟨h.vc, ⟨hh, e, h.hint hh e⟩, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    rw [h.r11, e, show VG.Proof.MlDsa.Arm.Verify.zOk p σ 0 = true from decide_eq_true fun _ h => absurd h (Nat.not_lt_zero _)]
    rfl

omit hP hF hS in
theorem v1_out {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.V1 p STK σ s) (hv : VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.hintOf p σ).isSome = 0) : VG.Proof.MlDsa.Arm.Verify.VFin p STK σ s := by
  refine ⟨h.vc, .inr ⟨h.r11.trans hv, ?_⟩⟩
  have e : VG.Proof.MlDsa.Arm.Verify.hintOf p σ = none := Option.not_isSome_iff_eq_none.mp (by rw [VG.Proof.MlDsa.Arm.Verify.flag_eq hv]; nofun)
  show verifyMu p minBounds _ _ _ ≠ some true
  rw [verifyMu_hint_none minBounds _ _ e]
  nofun

theorem body_piece : VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => VG.Proof.MlDsa.Arm.Verify.VC p STK σ s ∧ s.gpr .r11 = 1) (VG.Proof.MlDsa.Arm.Verify.VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (VG.Proof.MlDsa.Arm.Verify.hint_piece hP hF hS).seq (VG.Proof.MlDsa.Arm.Verify.ifOk_piece (v := fun σ => VG.Proof.MlDsa.Arm.Verify.flag (VG.Proof.MlDsa.Arm.Verify.hintOf p σ).isSome) (fun _ _ _ h => h.r11)
    (fun σ₁ σ₂ _ _ pub => ?_) (fun _ _ _ _ h => h.flags) ?_ fun _ _ _ h hv => VG.Proof.MlDsa.Arm.Verify.v1_out h hv)
  · have e : VG.Proof.MlDsa.Arm.Verify.sgOf p σ₁ = VG.Proof.MlDsa.Arm.Verify.sgOf p σ₂ := pub.2.2.2.2.2.2.2
    dsimp only [VG.Proof.MlDsa.Arm.Verify.hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.Arm.Verify.V2 p STK j) p.ℓ 0
      fun j _ hj => VG.Proof.MlDsa.Arm.Verify.zOne_piece hP hF hS (by omega)) (fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.v1_v2 h.1 h.2) fun _ _ _ h => ?_)
      (VG.Proof.MlDsa.Arm.Verify.inner_piece hP hF hS)
    rwa [Nat.zero_add] at h

end

/-! ## The return -/

theorem vepi_ok {p : Params} {STK : Nat} {σ s : State} (h : VG.Proof.MlDsa.Arm.Verify.VFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      Arm.target.abiPreserved σ s' ∧ (Spec.MlDsa.verifyContract p Arm.abi STK).post σ s' := by
  obtain ⟨vc, hr⟩ := h
  have hs := vc.site
  have e0 : ∀ o, (hashLay (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ) s VG.Proof.MlDsa.Arm.Verify.Kmu).A 0 o = (VG.Proof.MlDsa.Arm.Verify.vlay p STK σ).A 0 o := fun o => by
    simp only [Lay.A, hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx VG.Proof.MlDsa.Arm.Verify.kmu) (by rw [e0]; exact vc.sav) (by rw [e0]; exact vc.lr))
    fun s' ⟨pr, r0, m', sp'⟩ => ⟨⟨pr, sp'.trans vc.sp⟩, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, r0]
  exact hr

theorem vepi_piece {p : Params} {STK : Nat} :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (VG.Proof.MlDsa.Arm.Verify.VFin p STK)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p Arm.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => VG.Proof.MlDsa.Arm.Verify.vepi_ok h, VG.Proof.MlDsa.Arm.Verify.vrel7 (fun _ _ h => h.1) (by taint_decide)⟩

/-! ## The function -/

theorem verify_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.Arm.Verify.VFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) :
    VG.Proof.MlDsa.Arm.Verify.VPiece p STK (fun σ s => s = σ)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p Arm.abi STK).post σ s)
      (verify P p) :=
  (VG.Proof.MlDsa.Arm.Verify.vpro_piece hF (by omega)).seq ((VG.Proof.MlDsa.Arm.Verify.body_piece hP hF hS).seq VG.Proof.MlDsa.Arm.Verify.vepi_piece)

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_verify` of the parameter set `p` meets its contract with
36 bytes of stack, for any verified implementations `P` of the primitives
it calls with at most 28 bytes of stack. -/
theorem verify_verified {P : Prims} (hP : VG.Proof.MlDsa.Arm.Verify.VPrimsOk P 28) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified Arm.target (verify P p) (Spec.MlDsa.verifyContract p Arm.abi 36) := by
  have hF := VG.Proof.MlDsa.Arm.Verify.vfacts hp
  have hk := VG.Proof.MlDsa.Arm.Verify.verify_piece hP hF (STK := 36) (Nat.le_refl _)
  refine ⟨fun s hs => hk.ok s s (VG.Proof.MlDsa.Arm.Verify.vpre_of (n := 35) hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
      (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
    obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
    exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (VG.Proof.MlDsa.Arm.Verify.vpre_of (n := 35) h₁) (VG.Proof.MlDsa.Arm.Verify.vpre_of (n := 35) h₂)
      ⟨hsp, h0, h1, h2, h3, e1, e2, e3⟩ e₁ e₂
  · refine ⟨VG.Proof.MlDsa.Arm.Verify.verifySat p, ?_⟩
    rcases hp with rfl | rfl | rfl <;>
    sig_sat_check [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, VG.Proof.MlDsa.Arm.Verify.verifySat]

end VG.Proof.MlDsa.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst`. -/
section

/-!
# ML-DSA verification on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives (`prims`) are verified with at most
28 bytes of stack, and their frames use no more (`prims_ok`), so verification
with them is verified with 36 (`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm
open VG.Impl.MlDsa.Arm.Verify

theorem prims_ok : VG.Proof.MlDsa.Arm.Verify.VPrimsOk VG.Impl.MlDsa.Arm.Verify.prims 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨8, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨12, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨4, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨16, by decide, Pack.Hint.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨4, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem verify44_verified :
    Verified Arm.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.Verify.verify_verified VG.Proof.MlDsa.Arm.Verify.prims_ok _ (.inl rfl)

theorem verify65_verified :
    Verified Arm.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.Verify.verify_verified VG.Proof.MlDsa.Arm.Verify.prims_ok _ (.inr (.inl rfl))

theorem verify87_verified :
    Verified Arm.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 Arm.abi 36) :=
  VG.Proof.MlDsa.Arm.Verify.verify_verified VG.Proof.MlDsa.Arm.Verify.prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Verify

end
