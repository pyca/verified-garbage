module

public import VerifiedGarbage.Proof.RsaPss.X86_64.Back
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: one candidate salt length

The blocks of `cand`, for the candidate `c` (in `sCtr`, word 19): the
arguments of `finalize` of the state after the prefix and `c` bytes, to
`scratch + oLh` (`finCandArgs_ok`), and of `update` of it with the buffer's
byte `c` (`updCandArgs_ok`); the 64 bytes at `oLh` to `oDig` under the mask
of `c = L` (`selCand_ok`, `L` in word 5); and the next candidate
(`nextCand_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sCtr sHD oBuf oSt oDig oLh oW oRsa scr lay)
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd ea_sp ea_ix0 ofNat_add_lit off_plus nW slot_eq stepI_ok byteLoop_ok sel_byte
  xor_lt_one sx_lit trunc_zext)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)

/-- `finalize`'s arguments for the candidate `c`, to `scratch + oLh`. -/
theorem finCandArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D c : Nat} (hD : W 39 = BitVec.ofNat 64 D) (hc : W 19 = BitVec.ofNat 64 c) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sCtr))] : List Instr) ++ scr .rdx oLh ++ scr .rcx oW)) u
      fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + c) ∧ u'.gpr .rdx = off S oLh ∧
        u'.gpr .rcx = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + c) ∧ u'.gpr .rdx = off S oLh ∧ u'.gpr .rcx = off S oW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c', d, f⟩, k⟩ => ⟨a, b, c', d, f, k⟩
  xrun [scr, plen, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), L.ld (d := sCtr) (by decide), hs,
    R.rd (d := sHD) 39 rfl (by decide), R.rd (d := sCtr) 19 rfl (by decide), hD, hc, ofNat_add_lit,
    BitVec.ofNat_add, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oLh < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- `update`'s arguments for the candidate `c`: the buffer's byte `c`. -/
theorem updCandArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {D c : Nat} (hD : W 39 = BitVec.ofNat 64 D) (hc : W 19 = BitVec.ofNat 64 c) :
    WP isa (.block (scr .rdi oSt ++ plen ++ ([.alu .add .rsi (.mem (sp sCtr))] : List Instr) ++ scr .rdx oBuf ++
      ([.alu .add .rdx (.mem (sp sCtr)), .mov32 .rcx (.imm 1)] : List Instr) ++ scr .r8 oW)) u
      fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + c) ∧
        u'.gpr .rdx = off S (oBuf + c) ∧ u'.gpr .rcx = BitVec.ofNat 64 1 ∧ u'.gpr .r8 = off S oW ∧
        u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (D + 8 + c) ∧ u'.gpr .rdx = off S (oBuf + c) ∧
      u'.gpr .rcx = BitVec.ofNat 64 1 ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl)
    fun u' ⟨⟨a, b, c', d, f, g⟩, k⟩ => ⟨a, b, c', d, f, g, k⟩
  xrun [scr, plen, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sHD) (by decide), L.ld (d := sCtr) (by decide), hs,
    R.rd (d := sHD) 39 rfl (by decide), R.rd (d := sCtr) 19 rfl (by decide), hD, hc, ofNat_add_lit,
    BitVec.ofNat_add, off_plus, VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- The 64 bytes at `oDig`, those at `oLh` if `c`. -/
def selV (V : Nat → Byte) (c : Bool) (j : Nat) (x : Nat) : Byte :=
  if oDig ≤ x ∧ x < oDig + j then (if c then V (oLh + (x - oDig)) else V x) else V x

/-- The invariant of `selCand`'s loop after `j` bytes. -/
structure SelI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (c : Bool) (j : Nat) (v : State) :
    Prop where
  L : Lay v F S
  keep : Keep [.rax, .rdx, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (selV V c j) W

/-- The digest of the candidate `c` (64 bytes at `oLh`) to `oDig` if `c = L`. -/
theorem selCand_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c l : Nat} (hc : W 19 = BitVec.ofNat 64 c) (hl : W 5 = BitVec.ofNat 64 l)
    (hc64 : c < 2 ^ 64) (hl64 : l < 2 ^ 64) :
    WP isa selCand u fun u' => Lay u' F S ∧ Keep [.rax, .r11, .rcx, .rdi, .r8, .rdx] u u' ∧
      Rep u'.mem F S (selV V (decide (c = l)) 64) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c2 : oDig = 3328 := rfl
  have c7 : oLh = 3392 := rfl
  have c5 : oRsa = 8192 := rfl
  unfold selCand
  refine WP.seq (WP.mono (WP.keep [.rax, .r11, .rcx, .rdi, .r8] (Q := fun v =>
      v.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (c = l))) ∧ v.gpr .rcx = off S oLh ∧
      v.gpr .rdi = off S oDig ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁₁, h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sCtr) (by decide), L.ld (d := sL) (by decide), hs,
      R.rd (d := sCtr) 19 rfl (by decide), R.rd (d := sL) 5 rfl (by decide), hc, hl, xor_lt_one hc64 hl64,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLh < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (byteLoop_ok (n := 64) (by decide) (stepI_ok (show 64 < 2 ^ 31 by decide) v [.rax, .rdx, .r8])
    (SelI v F S V W (decide (c = l))) ?_ (u := v) ⟨Lv, Keep.refl _ _, h₃,
      (congrArg (fun V' => Rep v.mem F S V' W) (funext fun x => by simp only [selV]; rw [ifn (by omega)])).mpr
        (hm ▸ R)⟩)
    fun w I => ⟨I.L, (hk.trans I.keep).mono (by decide), I.R⟩
  intro j hj w I
  have hcv : w.gpr .rcx = off S oLh := (I.keep.gpr (by decide)).trans h₁
  have hdv : w.gpr .rdi = off S oDig := (I.keep.gpr (by decide)).trans h₂
  have hmv : w.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (c = l))) :=
    (I.keep.gpr (by decide)).trans h₁₁
  have va : w.mem (off S (oLh + j)) = V (oLh + j) := by
    rw [I.R.scr _ (by omega), selV, ifn (by omega)]
  have vb : w.mem (off S (oDig + j)) = V (oDig + j) := by
    rw [I.R.scr _ (by omega), selV, ifn (by omega)]
  have hv : (if decide (c = l) then V (oLh + j) else V (oDig + j)) =
      (BitVec.setWidth 64 (V (oDig + j)) ^^^ ((BitVec.setWidth 64 (V (oLh + j)) ^^^ BitVec.setWidth 64 (V (oDig + j))) &&&
        (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (c = l)))))).setWidth 8 := (sel_byte _ _ _).symm
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = w.mem.writeW (off S (oDig + j)) (if decide (c = l) then V (oLh + j) else V (oDig + j))) ?_ rfl)
    fun v' ⟨⟨h8', hm'⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm'' h8'' => ?_⟩
  · rw [hv]
    xrun [ea_ix0, hcv, hdv, hmv, I.r8, off_plus, I.L.sld8 (d := oLh + j) (by omega),
      I.L.sld8 (d := oDig + j) (by omega), I.L.sst8 (d := oDig + j) (by omega), va, vb]
  · have R' := I.R.wb I.L.geo (o := oDig + j) (by omega) (if decide (c = l) then V (oLh + j) else V (oDig + j))
    rw [← hm', ← hm''] at R'
    have R'' : Rep v''.mem F S (selV V (decide (c = l)) (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, selV]
      by_cases hx : x = oDig + j
      · subst hx
        simp only [ite_true, show oDig ≤ oDig + j ∧ oDig + j < oDig + (j + 1) by omega,
          Nat.add_sub_cancel_left, and_self]
      · by_cases h' : oDig ≤ x ∧ x < oDig + j
        · simp only [hx, h', show oDig ≤ x ∧ x < oDig + (j + 1) by omega, and_self, ite_true, ite_false]
        · simp only [hx, h', show ¬(oDig ≤ x ∧ x < oDig + (j + 1)) by omega, ite_false]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

/-- The next candidate, and ZF set iff it is `db`. -/
theorem nextCand_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {c db : Nat} (hc : W 19 = BitVec.ofNat 64 c) (hdb : W 44 = BitVec.ofNat 64 db)
    (hc1 : c + 1 < 2 ^ 64) (hdb' : db < 2 ^ 64) :
    WP isa (.block nextCand) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      u'.zf = some (decide (c + 1 = db)) ∧ Rep u'.mem F S V (upd W 19 (BitVec.ofNat 64 (c + 1))) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 19) (by decide) (BitVec.ofNat 64 (c + 1))
  rw [show off F (8 * 19) = off F sCtr from rfl] at R1
  have h44 : (u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))).readW (off F sDb) 64 = BitVec.ofNat 64 db := by
    have := R1.fr 44 (by decide); simp only [upd, Nat.reduceEqDiff, ite_false] at this; rw [← hdb, ← this]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.zf = some (decide (c + 1 = db)) ∧
      u'.mem = u.mem.writeW (off F sCtr) (BitVec.ofNat 64 (c + 1))) ?_ rfl)
    fun u' ⟨⟨hz, hm⟩, hk⟩ => ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hz, hm ▸ R1⟩
  xrun [nextCand, ea_sp, L.rsp, L.ld (d := sCtr) (by decide), L.st (d := sCtr) (by decide),
    L.ld (d := sDb) (by decide), R.rd (d := sCtr) 19 rfl (by decide), hc, h44, ofNat_add_lit,
    VG.Proof.Bignum.X86_64.ofNat_sub_beq hc1 hdb']

/-- The first candidate, 0. -/
theorem ctr0_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp sCtr) .rax]) u fun u' => Lay u' F S ∧ Keep [.rax] u u' ∧
      Rep u'.mem F S V (upd W 19 (BitVec.ofNat 64 0)) := by
  have R1 := R.wf L.geo (k := 19) (by decide) (BitVec.ofNat 64 0)
  rw [show off F (8 * 19) = off F sCtr from rfl] at R1
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F sCtr) (BitVec.ofNat 64 0)) ?_ rfl)
    fun u' ⟨hm, hk⟩ => ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R1⟩
  xrun [ea_sp, L.rsp, L.st (d := sCtr) (by decide), show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]

end VG.Proof.RsaPss.X86_64
