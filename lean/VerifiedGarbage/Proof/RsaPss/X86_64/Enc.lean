module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
public import VerifiedGarbage.Spec.RsaPss
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS on x86-64: the pieces of the encoding

`M'`'s prefix `0⁸ ‖ mHash` at `scratch + oMp` (`mPrefix_ok`); `0x01` and the
salt at the end of `DB` (`putSalt_ok`); `H` after `DB` and `0xbc` at the end
of `EM` (`putH_ok`); MGF1's slots for masking `DB` with `H` (`mgfArgs_ok`);
and the top bits of `DB`'s first byte cleared (`clearTop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sK sHD sSrc sSrcLen sDst sDstLen oEm oDig oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd slot_eq ea_sp ea_at0 ea_ix ofNat_add_lit off_plus off_sub off_sub1 nW
  cpV clrV copy_ok copyFrom_ok stepR_ok stepI_ok cpV_zero ofNat_beq_zero mW mW_args stBytes WP.seq_assoc trunc_zext)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- The bytes of `M'`'s prefix, over `V`: 8 zeros at `oMp`, the digest `src`
after them. -/
def mpV (V src : Nat → Byte) (D : Nat) : Nat → Byte := stBytes (0#64) oMp (cpV V src (oMp + 8) D)

theorem zeros8_len : (Spec.RsaPss.zeros 8).length = 8 := List.length_replicate

theorem mpV_bytes (V src : Nat → Byte) (D : Nat) :
    (List.range (D + 8)).map (fun i => mpV V src D (oMp + i)) =
      Spec.RsaPss.zeros 8 ++ (List.range D).map src := by
  apply List.ext_getElem (by rw [List.length_append, zeros8_len]; simp; omega)
  intro i h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range]
  simp only [mpV, stBytes, cpV]
  by_cases hi : i < 8
  · rw [ifp (by omega), List.getElem_append_left (by rw [zeros8_len]; exact hi)]
    simp only [Spec.RsaPss.zeros, List.getElem_replicate]
    simp
  · rw [ifn (by omega), ifp (by omega), List.getElem_append_right (by rw [zeros8_len]; omega)]
    rw [List.getElem_map, List.getElem_range]
    simp only [zeros8_len]
    exact congrArg src (by omega)

/-- `M'`'s prefix: the `D` bytes of the digest at `p` (word 27) to
`scratch + oMp + 8`, and the 8 bytes before them cleared. -/
theorem mPrefix_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D : Nat} {p : Addr} (hp : W 27 = p) (hD : W 39 = BitVec.ofNat 64 D)
    (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hsrc : ∀ i < D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < D, ∀ j < D, p + BitVec.ofNat 64 i ≠ off S (oMp + 8 + j)) :
    WP isa mPrefix u fun u' => Lay u' F S ∧ Keep [.rsi, .rcx, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (mpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) D) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  unfold mPrefix seqs seqs
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .r10, .r8] (Q := fun v => v.gpr .rsi = p ∧ v.gpr .rcx = off S oMp ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.gpr .r10 = BitVec.ofNat 64 D ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨a₁, a₂, a₃, a₄, hm⟩, kv⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sDig) (by decide), L.ld (d := sHD) (by decide), hs,
      R.rd (d := sDig) 27 rfl (by decide), R.rd (d := sHD) 39 rfl (by decide), hp, hD,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oMp < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [hm])
  have hsrc' : ∀ i < D, InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [kv.2.1, kv.2.2]; exact hsrc i hi
  refine WP.seq (WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (o := oMp) (disp := 8)
    (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) a₄) hD0
    (by unfold oMp oRsa; omega) a₁ a₂ a₃ hsrc' hdis) fun w ⟨Lw, kw, Rw⟩ => ?_)
  have hcw : w.gpr .rcx = off S oMp := (kw.gpr (by decide)).trans a₂
  rw [hm] at Rw
  have R2 := Rw.ws Lw.geo (o := oMp) (w := 64) (by unfold oMp oRsa; omega) (0#64)
  refine WP.mono (WP.keep [.rax] (Q := fun x => x.mem = w.mem.writeW (off S oMp) (0#64)) ?_ rfl)
    fun x ⟨hmx, kx⟩ => ⟨Lw.of_rep Rw (hmx ▸ R2) (kx.gpr (by decide)) kx.2.2,
      (kv.trans (kw.trans kx)).mono (by decide), hmx ▸ R2⟩
  xrun [ea_at0, hcw, Lw.sst (d := oMp) (by unfold oMp oRsa; omega)]
  rfl

/-- `EM` with `0x01` before the salt, at `e + db - sl - 1`. -/
theorem putSalt_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db sl : Nat} {q : Addr} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hq : W 28 = q) (hsl : W 29 = BitVec.ofNat 64 sl) (hfit : sl + 1 ≤ db) (hend : e + db ≤ oRsa)
    (hsrc : ∀ i < sl, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < sl, ∀ j < sl + 1, q + BitVec.ofNat 64 i ≠ off S (e + db - sl - 1 + j)) :
    WP isa putSalt u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .r10, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV (upd V (e + db - sl - 1) 1) (fun i => u.mem (q + BitVec.ofNat 64 i))
        (e + db - sl - 1 + 1) sl) W := by
  have G := L.geo
  have R1 := R.wb G (o := e + db - sl - 1) (by omega) (1 : Byte)
  refine WP.seq (WP.mono (WP.keep [.rdi, .rax] (Q := fun v => v.gpr .rdi = off S (e + db - sl - 1) ∧
      v.mem = u.mem.writeW (off S (e + db - sl - 1)) (1 : Byte)) ?_ rfl) fun v ⟨⟨h₁, hm⟩, hk⟩ => ?_)
  · have ea : off S e + BitVec.ofNat 64 db - BitVec.ofNat 64 sl - 1 = off S (e + db - sl - 1) := by
      rw [off_plus, off_sub S (by omega), off_sub1 S (by omega)]
    xrun [putSalt, ea_sp, ea_at0, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sSaltLen) (by decide), R.rd (d := sEb) 33 rfl (by decide), R.rd (d := sDb) 44 rfl (by decide),
      R.rd (d := sSaltLen) 29 rfl (by decide), he, hdb, hsl, ea, L.sst8 (d := e + db - sl - 1) (by omega)]
    rfl
  have R1' : Rep v.mem F S (upd V (e + db - sl - 1) 1) W := hm ▸ R1
  have Lv : Lay v F S := L.of_rep R R1' (hk.gpr (by decide)) hk.2.2
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun w => w.gpr .rsi = q ∧
      w.gpr .r10 = BitVec.ofNat 64 sl ∧ w.gpr .r8 = BitVec.ofNat 64 0 ∧ w.zf = some (decide (sl = 0)) ∧
      w.mem = v.mem) ?_ rfl) fun w ⟨⟨h₂, h₁₀, h₈, hz, hm'⟩, hk'⟩ => ?_)
  · xrun [ea_sp, Lv.rsp, Lv.ld (d := sSalt) (by decide), Lv.ld (d := sSaltLen) (by decide),
      R1'.rd (d := sSalt) 28 rfl (by decide), R1'.rd (d := sSaltLen) 29 rfl (by decide), hq, hsl]
    rw [BitVec.and_self, ofNat_beq_zero (by unfold oRsa at hend; omega)]
  have Lw : Lay w F S := Lv.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm'])
  have hsrc' : ∀ i < sl, u.mem (q + BitVec.ofNat 64 i) = w.mem (q + BitVec.ofNat 64 i) := fun i hi => by
    rw [hm', hm, VG.WriteBytes.writeW8_apply, ifn (fun h => hdis i hi 0 (by omega) (by rw [h]; rfl))]
  refine WP.ite (M := isa) _ (show isa.eval .e w = _ from hz) (fun hb => ?_) (fun hb => ?_)
  · rw [decide_eq_true_eq] at hb
    subst hb
    refine WP.mono (WP.keep [] (Q := fun x => x = w) ?_ rfl) fun x ⟨hx, _⟩ => ?_
    · xrun
    · subst hx
      exact ⟨Lw, (hk.trans hk').mono (by decide), by rw [cpV_zero, hm']; exact R1'⟩
  · rw [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok Lw (hm' ▸ R1') (d := .rdi) (by decide) (p := q) (o := e + db - sl - 1) (disp := 1)
      (n := sl) (stepR_ok (by unfold oRsa at hend; omega) w (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀)
      (by omega) (by omega) h₂ ((hk'.gpr (by decide)).trans h₁) h₈
      (fun i hi => by rw [hk'.2.1, hk'.2.2, hk.2.1, hk.2.2]; exact hsrc i hi)
      (fun i hi j hj => by
        have := hdis i hi (1 + j) (by omega)
        rwa [show e + db - sl - 1 + (1 + j) = e + db - sl - 1 + 1 + j by omega] at this))
      fun x ⟨Lx, kx, Rx⟩ => ⟨Lx, (hk.trans (hk'.trans kx)).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep x.mem F S V' W) (funext fun y => ?_)).mp Rx
    simp only [cpV]
    split
    · rw [hsrc' _ (by omega)]
    · rfl

/-- `H`, the digest at `scratch + oDig`, after `DB`. -/
theorem putHd_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db k D : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hD : W 39 = BitVec.ofNat 64 D) (hD0 : 0 < D) (hD64 : D ≤ 64) (hend : e + db + D + 1 = oEm + k)
    (hk2 : k ≤ 1024) :
    WP isa (.seq (.block (([.mov .rdi (.mem (sp sEb)), .mov .rax (.mem (sp sDb)), .alu .add .rdi (.reg .rax)] : List Instr) ++
        scr .rsi oDig ++ ([.mov .r10 (.mem (sp sHD)), .mov32 .r8 (.imm 0)] : List Instr)))
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8) .rax] (.reg .r10))) u fun u' =>
      Lay u' F S ∧ Keep [.rdi, .rsi, .rax, .r8, .r10] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (oDig + i)) (e + db) D) W := by
  have c1 : oEm = 0 := rfl
  have c3 : oDig = 3328 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .r10, .r8, .rax] (Q := fun v => v.gpr .rdi = off S (e + db) ∧
      v.gpr .rsi = off S oDig ∧ v.gpr .r10 = BitVec.ofNat 64 D ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₁₀, h₃, hm⟩, hkv⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sHD) (by decide), R.rd (d := sEb) 33 rfl (by decide), R.rd (d := sDb) 44 rfl (by decide),
      R.rd (d := sHD) 39 rfl (by decide), he, hdb, hD, off_plus,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hkv.gpr (by decide)) hkv.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (copy_ok Lv Rv (d := .rdi) (by decide) (p := off S oDig) (o := e + db) (disp := 0)
    (n := D) (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₁₀) hD0
    (by unfold oRsa; omega) h₂ h₁ h₃
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hkv.trans kw).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa; omega)]
  · rfl

/-- `0xbc` at the end of `EM`. -/
theorem putBc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) :
    WP isa (.block (scr .rdi oEm ++ ([.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .alu .sub .rdi (.imm 1),
        .mov32 .rax (.imm 0xbc), .store8 (at_ .rdi) .rax] : List Instr))) u fun u' =>
      Lay u' F S ∧ Keep [.rdi, .rax] u u' ∧ Rep u'.mem F S (upd V (oEm + k - 1) 0xbc) W := by
  have c1 : oEm = 0 := rfl
  have hs := L.slot
  simp only [Bignum.word] at hs
  have R2 := R.wb L.geo (o := oEm + k - 1) (by unfold oRsa; omega) (0xbc : Byte)
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun x => x.mem = u.mem.writeW (off S (oEm + k - 1)) (0xbc : Byte))
    ?_ rfl) fun x ⟨hmx, kx⟩ => ⟨L.of_rep R (hmx ▸ R2) (kx.gpr (by decide)) kx.2.2, kx, hmx ▸ R2⟩
  xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp,
    L.ld (d := sScr) (by decide), hs, L.ld (d := sK) (by decide), R.rd (d := sK) 23 rfl (by decide), hk,
    off_plus, off_sub1 S (show 1 ≤ oEm + k by omega),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), L.sst8 (d := oEm + k - 1) (by unfold oRsa; omega)]
  rfl

/-- `H`, the digest at `scratch + oDig`, after `DB`, and `0xbc` at the end of
`EM`. -/
theorem putH_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db k D : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hk : W 23 = BitVec.ofNat 64 k) (hD : W 39 = BitVec.ofNat 64 D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hend : e + db + D + 1 = oEm + k) (hk2 : k ≤ 1024) :
    WP isa putH u fun u' => Lay u' F S ∧ Keep [.rdi, .rsi, .rax, .r8, .r10] u u' ∧
      Rep u'.mem F S (upd (cpV V (fun i => V (oDig + i)) (e + db) D) (oEm + k - 1) 0xbc) W := by
  unfold putH
  exact WP.seq_assoc (WP.seq (WP.mono (putHd_ok L R he hdb hD hD0 hD64 hend hk2) fun v ⟨Lv, kv, Rv⟩ =>
    WP.mono (putBc_ok Lv Rv hk (by unfold oEm at hend; omega) hk2) fun _ ⟨Lx, kx, Rx⟩ =>
      ⟨Lx, (kv.trans kx).mono (by decide), Rx⟩))

theorem trunc_and (x y : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x &&& BitVec.setWidth 64 y) = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ y.isLt)

/-- The top bits of `maskedDB`'s first byte cleared by the mask in `sC`. -/
theorem clearTop_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e : Nat} {c : Byte} (he : W 33 = off S e) (hc : W 30 = BitVec.setWidth 64 c)
    (he1 : e < oRsa) :
    WP isa (.block clearTop) u fun u' => Lay u' F S ∧ Keep [.rdi, .rax] u u' ∧
      Rep u'.mem F S (upd V e (V e &&& c)) W := by
  have R2 := R.wb L.geo (o := e) he1 (V e &&& c)
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun x => x.mem = u.mem.writeW (off S e) (V e &&& c))
    ?_ rfl) fun x ⟨hmx, kx⟩ => ⟨L.of_rep R (hmx ▸ R2) (kx.gpr (by decide)) kx.2.2, kx, hmx ▸ R2⟩
  xrun [clearTop, ea_sp, ea_at0, L.rsp, L.ld (d := sEb) (by decide), R.rd (d := sEb) 33 rfl (by decide), he,
    L.sld8 (d := e) (by omega), R.scr e he1, L.ld (d := sC) (by decide), R.rd (d := sC) 30 rfl (by decide), hc,
    L.sst8 (d := e) (by omega)]
  rw [trunc_and]

/-- MGF1's slots for masking `DB` (`db` bytes at `e`) with `H` (`D` bytes
after it). -/
theorem mgfArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {e db D : Nat} (he : W 33 = off S e) (hdb : W 44 = BitVec.ofNat 64 db)
    (hD : W 39 = BitVec.ofNat 64 D) :
    WP isa (.block mgfArgs) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx, .rcx, .r9] u u' ∧
      Rep u'.mem F S V (mW W S (e + db) D e db) := by
  have G' := L.geo
  have R1 := (((R.wf G' (k := 17) (by decide) (off S e)).wf G' (k := 18) (by decide)
    (BitVec.ofNat 64 db)).wf G' (k := 15) (by decide) (off S (e + db))).wf G' (k := 16) (by decide)
    (BitVec.ofNat 64 D)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r9] (Q := fun u' => u'.mem =
      (((u.mem.writeW (off F (8 * 17)) (off S e)).writeW (off F (8 * 18))
        (BitVec.ofNat 64 db)).writeW (off F (8 * 15)) (off S (e + db))).writeW (off F (8 * 16))
        (BitVec.ofNat 64 D)) ?_ rfl) fun u' ⟨hm, kk⟩ => ⟨?_, kk, by rw [hm]; exact R1⟩
  · xrun [mgfArgs, ea_sp, L.rsp, L.ld (d := sEb) (by decide), L.ld (d := sDb) (by decide),
      L.ld (d := sHD) (by decide), R.rd (d := sEb) 33 rfl (by decide), R.rd (d := sDb) 44 rfl (by decide),
      R.rd (d := sHD) 39 rfl (by decide), he, hdb, hD, off_plus,
      L.st (d := sDst) (by decide), L.st (d := sDstLen) (by decide), L.st (d := sSrc) (by decide),
      L.st (d := sSrcLen) (by decide)]
    rfl
  · exact L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2

end VG.Proof.RsaPss.X86_64
