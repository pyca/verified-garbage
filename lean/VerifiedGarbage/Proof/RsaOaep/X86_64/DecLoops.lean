import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-!
# RSAES-OAEP decryption on x86-64: the loops of the decoding

Each loop of `decMain` after MGF1, as a function of the working space's
bytes (`V`) and the frame's words: the comparison of `lHash'` with `lHash`
(`accLh_ok`, `accL`), the scan of `T` (`scan_ok`, `scanS`), the buffer
cleared (`clearBuf_ok`), `T` copied to it (`copyT_ok`), one pass of the
shift (`shiftPass_ok`), and `out` (`outLoop_ok`).
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-! ## `lHash'` against `lHash` -/

/-- `EM[0] ∨ ⋁_{i < j} (lHash[i] ⊕ lHash'[i])`, as the code accumulates it. -/
def accL (V : Nat → Byte) (D : Nat) : Nat → BitVec 64
  | 0 => (V oEm).setWidth 64
  | j + 1 => accL V D j ||| ((V (oLh + j)).setWidth 64 ^^^ (V (oEm + 1 + D + j)).setWidth 64)

structure AccI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (D j : Nat) (v : State) :
    Prop where
  L : Lay v F S
  keep : Keep [.rax, .r9, .rdx, .r8] u₀ v
  mem : v.mem = u₀.mem
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  rdx : v.gpr .rdx = accL V D j

theorem accLh_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hD : 0 < Hm.D) (hD64 : Hm.D ≤ 64) :
    WP isa (accLh Hm) u fun u' => Lay u' F S ∧ Keep [.rcx, .rdi, .rsi, .rdx, .r8, .rax, .r9] u u' ∧
      Rep u'.mem F S V (upd W 31 (accL V Hm.D Hm.D)) := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c1 : oLh = 3392 := rfl
  have c2 : oEm = 0 := rfl
  have z : BitVec.ofNat 64 0 = 0#64 := rfl
  unfold accLh
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdi, .rsi, .rdx, .r8] (Q := fun v => v.gpr .rcx = off S oLh ∧
      v.gpr .rdi = off S (oEm + 1 + Hm.D) ∧ v.gpr .rdx = (V oEm).setWidth 64 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, ea_at0, L.rsp,
      L.ld (d := sScr) (by decide), hs, L.sld8 (d := oEm) (by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLh < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 + Hm.D < 2 ^ 31 by omega),
      show off S oEm = S + BitVec.ofNat 64 oEm from rfl, ← R.scr oEm (by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.seq (WP.mono (byteLoop_ok hD (stepI_ok (by omega) v [.rax, .r9, .rdx, .r8]) (AccI v F S V W Hm.D) ?_
    ⟨Lv, Keep.refl _ _, rfl, h₄, h₃⟩) fun w I => ?_)
  · intro j hj w I
    have hcw : w.gpr .rcx = off S oLh := (I.keep.gpr (by decide)).trans h₁
    have hdw : w.gpr .rdi = off S (oEm + 1 + Hm.D) := (I.keep.gpr (by decide)).trans h₂
    have va : w.mem (off S (oLh + j)) = V (oLh + j) := by rw [I.mem, hm, R.scr _ (by unfold oRsa; omega)]
    have vb : w.mem (off S (oEm + 1 + Hm.D + j)) = V (oEm + 1 + Hm.D + j) := by
      rw [I.mem, hm, R.scr _ (by unfold oRsa; omega)]
    refine WP.mono (WP.keep [.rax, .r9, .rdx] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧ w'.mem = w.mem ∧
        w'.gpr .rdx = accL V Hm.D (j + 1)) ?_ rfl)
      fun w' ⟨⟨h8', hm', hdx'⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun w'' k' hm'' h8'' => ?_⟩
    · xrun [ea_ix0, hcw, hdw, I.r8, off_plus, I.L.sld8 (d := oLh + j) (by unfold oRsa; omega),
        I.L.sld8 (d := oEm + 1 + Hm.D + j) (by unfold oRsa; omega), va, vb, I.rdx, accL]
    · exact ⟨I.L.congr (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2) (by rw [hm'', hm', I.mem]),
        (I.keep.trans (k.trans k')).mono (by decide), by rw [hm'', hm', I.mem], h8'',
        by rw [k'.gpr (by decide), hdx']⟩
  refine WP.mono (WP.keep [] (Q := fun x => x.mem = w.mem.writeW (off F sAcc) (accL V Hm.D Hm.D)) ?_ rfl)
    fun x ⟨hmx, kx⟩ => ?_
  · xrun [ea_sp, I.L.rsp, I.L.st (d := sAcc) (by decide), I.rdx]
  have R' : Rep x.mem F S V (upd W 31 (accL V Hm.D Hm.D)) := by
    rw [hmx, I.mem, hm]; exact R.wf L.geo (k := 31) (by decide) _
  exact ⟨I.L.of_rep' (I.mem ▸ hm ▸ R) R' (by simp [upd]) (kx.gpr (by decide)) kx.2.2,
    ((hk.trans I.keep).trans kx).mono (by decide), R'⟩

/-! ## The scan of `T` -/

/-- All ones if `x` is zero, as `cmp x, 1; sbb x, x` computes it. -/
abbrev zM (x : BitVec 64) : BitVec 64 := if x = 0 then BitVec.allOnes 64 else 0

/-- The scan's registers after `j` bytes of `f`, from the accumulator `c₀`:
`rdx` all ones while no `0x01` has been seen, `rsi` the index of the first,
`rcx` the accumulator, ORed with a mask for each byte before it that is
neither `0x00` nor `0x01`. -/
def scanS (f : Nat → Byte) (c₀ : BitVec 64) : Nat → BitVec 64 × BitVec 64 × BitVec 64
  | 0 => (BitVec.allOnes 64, 0, c₀)
  | j + 1 =>
    let p := scanS f c₀ j
    let b := (f j).setWidth 64
    let z := zM b
    let o := zM (b ^^^ 1)
    (p.1 &&& (o ^^^ BitVec.allOnes 64), p.2.1 ||| (BitVec.ofNat 64 j &&& p.1 &&& o),
      p.2.2 ||| (((z ||| o) ^^^ BitVec.allOnes 64) &&& p.1))

/-- `T`, the bytes of `DB` after `lHash'`. -/
def tF (V : Nat → Byte) (D : Nat) (i : Nat) : Byte := V (oEm + 1 + 2 * D + i)

theorem sx_ones : BitVec.signExtend 64 (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 64 := by decide

theorem sbb_zM (x : BitVec 64) :
    x - x - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))) = zM x := cmp_sbb x

theorem sbb0_zM (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))) = zM x := by
  have := cmp_sbb x
  rw [BitVec.sub_self] at this
  exact this

structure ScanI (u₀ : State) (F S : Addr) (f : Nat → Byte) (c₀ : BitVec 64) (j : Nat) (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .r9, .r11, .rdx, .rsi, .rcx, .r8] u₀ v
  mem : v.mem = u₀.mem
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  rdx : v.gpr .rdx = (scanS f c₀ j).1
  rsi : v.gpr .rsi = (scanS f c₀ j).2.1
  rcx : v.gpr .rcx = (scanS f c₀ j).2.2

/-- The scan of `T`'s `t = k - 2 hLen - 1` bytes, with `k` in its slot and
the accumulator in `sAcc`: the accumulator ORed with the last `rdx`, and the
index, to their slots. -/
theorem scan_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hkD : 2 * Hm.D + 2 ≤ k) (hk1 : k ≤ 1024)
    (hD64 : Hm.D ≤ 64) :
    WP isa (scan Hm) u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rdx, .rsi, .rcx, .r8, .rax, .r9, .r11] u u' ∧
      Rep u'.mem F S V (upd (upd W 31 ((scanS (tF V Hm.D) (W 31)
        (k - (2 * Hm.D + 1))).2.2 ||| (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).1))
        32 (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.1) := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have c2 : oEm = 0 := rfl
  unfold scan
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rdx, .rsi, .rcx, .r8] (Q := fun v =>
      v.gpr .rdi = off S (oEm + 1 + 2 * Hm.D) ∧ v.gpr .r10 = BitVec.ofNat 64 (k - (2 * Hm.D + 1)) ∧
      v.gpr .rdx = BitVec.allOnes 64 ∧ v.gpr .rsi = 0 ∧ v.gpr .rcx = W 31 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, hm⟩, hk'⟩ => ?_)
  · xrun [scr, Impl.Mgf1.X86_64.scr, lay, tLen, im, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), L.ld (d := sAcc) (by decide), hs,
      R.slot (d := sK) (k := 23) rfl (by decide) hk, R.slot (d := sAcc) (k := 31) rfl (by decide) rfl,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 + 2 * Hm.D < 2 ^ 31 by omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 1 < 2 ^ 31 by omega), sx_ones,
      VG.Offset.ofNat_sub_ofNat (show 2 * Hm.D + 1 ≤ k by omega)]
  have Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  have ht : 0 < k - (2 * Hm.D + 1) := by omega
  refine WP.seq (WP.mono (byteLoop_ok ht (stepR_ok (by omega) v
      (show Reg.r10 ∉ [Reg.rax, .r9, .r11, .rdx, .rsi, .rcx, .r8] by decide) (by decide) h₂)
    (ScanI v F S (tF V Hm.D) (W 31)) ?_ ⟨Lv, Keep.refl _ _, rfl, h₆, h₃, h₄, h₅⟩) fun w I => ?_)
  · intro j hj w I
    have hdw : w.gpr .rdi = off S (oEm + 1 + 2 * Hm.D) := (I.keep.gpr (by decide)).trans h₁
    have vb : w.mem (off S (oEm + 1 + 2 * Hm.D + j)) = tF V Hm.D j := by
      rw [I.mem, hm, R.scr _ (by unfold oRsa; omega)]; rfl
    refine WP.mono (WP.keep [.rax, .r9, .r11, .rdx, .rsi, .rcx] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.mem = w.mem ∧ w'.gpr .rdx = (scanS (tF V Hm.D) (W 31) (j + 1)).1 ∧
        w'.gpr .rsi = (scanS (tF V Hm.D) (W 31) (j + 1)).2.1 ∧
        w'.gpr .rcx = (scanS (tF V Hm.D) (W 31) (j + 1)).2.2) ?_ rfl)
      fun w' ⟨⟨h8', hm', hdx', hsi', hcx'⟩, k⟩ =>
        ⟨(I.keep.trans k).mono (by decide), h8', fun w'' k' hm'' h8'' => ?_⟩
    · xrun [scanBody, ea_ix0, hdw, I.r8, off_plus, I.L.sld8 (d := oEm + 1 + 2 * Hm.D + j) (by unfold oRsa; omega),
        vb, I.rdx, I.rsi, I.rcx, sbb_zM, sbb0_zM, sx_ones, scanS]
    · exact ⟨I.L.congr (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2)
          (by rw [hm'', hm', I.mem]),
        (I.keep.trans (k.trans k')).mono (by decide), by rw [hm'', hm', I.mem], h8'',
        by rw [k'.gpr (by decide), hdx'], by rw [k'.gpr (by decide), hsi'], by rw [k'.gpr (by decide), hcx']⟩
  have G' := L.geo
  have R1 := ((hm ▸ R : Rep v.mem F S V W).wf G' (k := 31) (by decide)
    ((scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.2 ||| (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).1)).wf
    G' (k := 32) (by decide) (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.1
  refine WP.mono (WP.keep [.rcx] (Q := fun x => x.mem = (w.mem.writeW (off F (8 * 31))
      ((scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.2 ||| (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).1)).writeW
      (off F (8 * 32)) (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.1) ?_ rfl) fun x ⟨hmx, kx⟩ => ?_
  · xrun [ea_sp, I.L.rsp, I.L.st (d := sAcc) (by decide), I.L.st (d := sIdx) (by decide), I.rdx, I.rsi, I.rcx]
    rfl
  have R' : Rep x.mem F S V (upd (upd W 31 ((scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.2 |||
      (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).1)) 32 (scanS (tF V Hm.D) (W 31) (k - (2 * Hm.D + 1))).2.1) := by
    rw [hmx, I.mem]; exact R1
  exact ⟨Lv.of_rep' (hm ▸ R) R' (by simp [upd]) (by rw [kx.gpr (by decide), I.keep.gpr (by decide)])
      (kx.2.2.trans I.keep.2.2), ((hk'.trans I.keep).trans kx).mono (by decide), R'⟩

/-! ## The buffer -/

/-- The buffer cleared, with `T`'s address and length and the buffer's in
`rsi`, `r10` and `rcx`. -/
theorem clearBuf_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k)
    (hkD : 2 * Hm.D + 2 ≤ k) (hD64 : Hm.D ≤ 64) :
    WP isa (clearBuf Hm) u fun u' => Lay u' F S ∧ Keep [.rsi, .r10, .rcx, .rax, .r8] u u' ∧
      u'.gpr .rsi = off S (oEm + 1 + 2 * Hm.D) ∧ u'.gpr .r10 = BitVec.ofNat 64 (k - (2 * Hm.D + 1)) ∧
      u'.gpr .rcx = off S oBuf ∧ Rep u'.mem F S (clrV V oBuf 2048) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .rcx, .rax, .r8] (Q := fun v =>
      v.gpr .rsi = off S (oEm + 1 + 2 * Hm.D) ∧ v.gpr .r10 = BitVec.ofNat 64 (k - (2 * Hm.D + 1)) ∧
      v.gpr .rcx = off S oBuf ∧ v.gpr .rax = 0 ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₀, h₁₀, h₁, h₂, h₃, hm⟩, hk'⟩ => ?_)
  · xrun [clearBuf, scr, Impl.Mgf1.X86_64.scr, lay, tLen, im, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), hs,
      R.slot (d := sK) (k := 23) rfl (by decide) hk,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 + 2 * Hm.D < 2 ^ 31 by unfold oEm; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show 2 * Hm.D + 1 < 2 ^ 31 by omega),
      VG.Offset.ofNat_sub_ofNat (show 2 * Hm.D + 1 ≤ k by omega)]
  have Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  refine WP.mono (clearQ_ok Lv (hm ▸ R) (o := oBuf) (n := 2048) (by decide) (by decide) (by decide) (by decide)
    h₁ h₂ h₃) fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk'.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₀,
      (kw.gpr (by decide)).trans h₁₀, (kw.gpr (by decide)).trans h₁, Rw⟩

/-- `T` (`t` bytes at `oEm + 1 + 2 hLen`, at `rsi`) to the buffer (at `rcx`). -/
theorem copyT_ok {Hm : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (h₁ : u.gpr .rsi = off S (oEm + 1 + 2 * Hm.D))
    (h₃ : u.gpr .r10 = BitVec.ofNat 64 (k - (2 * Hm.D + 1))) (h₂ : u.gpr .rcx = off S oBuf)
    (hkD : 2 * Hm.D + 2 ≤ k) (hk1 : k ≤ 1024) (hD64 : Hm.D ≤ 64) :
    WP isa copyT u fun u' => Lay u' F S ∧ Keep [.rax, .r8] u u' ∧ u'.gpr .rcx = off S oBuf ∧
      Rep u'.mem F S (cpV V (tF V Hm.D) oBuf (k - (2 * Hm.D + 1))) W := by
  have c2 : oEm = 0 := rfl
  have c3 : oBuf = 1024 := rfl
  unfold copyT
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun v => v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₄, hm⟩, hk'⟩ => ?_)
  · xrun []
  have Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  have h₂' : v.gpr .rcx = off S oBuf := (hk'.gpr (by decide)).trans h₂
  refine WP.mono (copy_ok Lv Rv (d := .rcx) (by decide) (p := off S (oEm + 1 + 2 * Hm.D)) (o := oBuf) (disp := 0)
    (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) ((hk'.gpr (by decide)).trans h₃))
    (by omega) (by unfold oRsa; omega) ((hk'.gpr (by decide)).trans h₁) h₂' h₄
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk'.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₂', ?_⟩
  refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by unfold oRsa; omega)]; rfl
  · rfl

/-! ## One pass of the shift -/

/-- The buffer's first `j` bytes replaced by those `d` after them if `b`. -/
def selV (V : Nat → Byte) (d : Nat) (b : Bool) (j : Nat) (x : Nat) : Byte :=
  if oBuf ≤ x ∧ x < oBuf + j then (if b then V (x + d) else V x) else V x

theorem neg_and1 (a : BitVec 64) :
    0#64 - (a &&& 1) = if a.toNat % 2 = 1 then BitVec.allOnes 64 else 0#64 := by
  have h : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one a.toNat with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

theorem selB (x y : Byte) (b : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 64 x ^^^ ((BitVec.setWidth 64 y ^^^ BitVec.setWidth 64 x) &&&
      (if b then BitVec.allOnes 64 else 0#64))) = if b then y else x := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm (BitVec.setWidth 64 y), ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    exact trunc_zext y

structure ShI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (d : Nat) (b : Bool) (j : Nat)
    (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .rdi, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (selV V d b j) W

/-- One pass, with the buffer at `rcx`: its first 1024 bytes replaced by
those `d` (`rdx`) after them if bit 0 of `a` (`sA`) is set. -/
theorem shiftPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {d : Nat} (hcx : u.gpr .rcx = off S oBuf) (hdx : u.gpr .rdx = BitVec.ofNat 64 d)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 1024) :
    WP isa shiftPass u fun u' => Lay u' F S ∧ Keep [.rsi, .r11, .r9, .r8, .rax, .rdi] u u' ∧
      Rep u'.mem F S (selV V d (decide ((W 34).toNat % 2 = 1)) 1024) W := by
  have c3 : oBuf = 1024 := rfl
  unfold shiftPass
  refine WP.seq (WP.mono (WP.keep [.rsi, .r11, .r9, .r8] (Q := fun v => v.gpr .rsi = off S (oBuf + d) ∧
      v.gpr .r9 = (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sA) (by decide), hcx, hdx, R.slot (d := sA) (k := 34) rfl (by decide) rfl,
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl, neg_and1]
    rw [BitVec.add_comm, off_plus]
  have h₁ : v.gpr .rcx = off S oBuf := (hk.gpr (by decide)).trans hcx
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (byteLoop_ok (n := 1024) (by decide) (stepI_ok (by decide) v [.rax, .rdi, .r8])
    (ShI v F S V W d (decide ((W 34).toNat % 2 = 1))) ?_ ⟨Lv, Keep.refl _ _, h₄,
      (congrArg (fun V' => Rep v.mem F S V' W) (funext fun x => by
        simp only [selV]; rw [ifn (by omega)])).mpr (hm ▸ R)⟩) fun w I => ⟨I.L, (hk.trans I.keep).mono (by decide), I.R⟩
  intro j hj w I
  have hcw : w.gpr .rcx = off S oBuf := (I.keep.gpr (by decide)).trans h₁
  have hsw : w.gpr .rsi = off S (oBuf + d) := (I.keep.gpr (by decide)).trans h₂
  have h9w : w.gpr .r9 = (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) := (I.keep.gpr (by decide)).trans h₃
  have va : w.mem (off S (oBuf + j)) = V (oBuf + j) := by
    rw [I.R.scr _ (by unfold oRsa; omega), selV, ifn (by omega)]
  have vb : w.mem (off S (oBuf + d + j)) = V (oBuf + j + d) := by
    rw [I.R.scr _ (by unfold oRsa; omega), selV, ifn (by omega), show oBuf + d + j = oBuf + j + d by omega]
  have e : (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) =
      (if decide ((W 34).toNat % 2 = 1) then BitVec.allOnes 64 else 0#64) := by simp
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
      w'.mem = w.mem.writeW (off S (oBuf + j))
        (if decide ((W 34).toNat % 2 = 1) then V (oBuf + j + d) else V (oBuf + j))) ?_ rfl)
    fun w' ⟨⟨h8', hm'⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun w'' k' hm'' h8'' => ?_⟩
  · xrun [ea_ix0, hcw, hsw, h9w, I.r8, off_plus, I.L.sld8 (d := oBuf + j) (by unfold oRsa; omega),
      I.L.sld8 (d := oBuf + d + j) (by unfold oRsa; omega), I.L.sst8 (d := oBuf + j) (by unfold oRsa; omega),
      va, vb, e, selB]
  · have R' := I.R.wb I.L.geo (o := oBuf + j) (by unfold oRsa; omega)
      (if decide ((W 34).toNat % 2 = 1) then V (oBuf + j + d) else V (oBuf + j))
    rw [← hm', ← hm''] at R'
    have R'' : Rep w''.mem F S (selV V d (decide ((W 34).toNat % 2 = 1)) (j + 1)) W := by
      refine (congrArg (fun V' => Rep w''.mem F S V' W) (funext fun x => ?_)).mp R'
      unfold upd selV
      by_cases hx : x = oBuf + j
      · subst hx
        rw [ifp (show oBuf + j = oBuf + j from rfl), ifp (show oBuf ≤ oBuf + j ∧ oBuf + j < oBuf + (j + 1) by omega)]
      · rw [ifn hx]
        by_cases h' : oBuf ≤ x ∧ x < oBuf + j
        · rw [ifp h', ifp (show oBuf ≤ x ∧ x < oBuf + (j + 1) by omega)]
        · rw [ifn h', ifn (show ¬ (oBuf ≤ x ∧ x < oBuf + (j + 1)) by omega)]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

/-! ## The shift -/

theorem shr1_ofNat {a : Nat} (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 1 = BitVec.ofNat 64 (a / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]

theorem dbl_ofNat (d : Nat) : BitVec.ofNat 64 d + BitVec.ofNat 64 d = BitVec.ofNat 64 (2 * d) := by
  rw [← BitVec.ofNat_add, Nat.two_mul]

theorem sub1_ofNat {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) :=
  VG.Offset.ofNat_sub_ofNat (d := 1) hj

theorem nextPass_eq : nextPass =
    ([.mov .rax (.mem (sp sA)), .shift .shr .rax 1, .store (sp sA) .rax] : List Instr) ++
    ([.alu .add .rdx (.reg .rdx), .alu .sub .r10 (.imm 1)] : List Instr) := rfl

/-- The next pass: `a / 2`, `2 d`, `j - 1`, and ZF set after the last. -/
theorem nextPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d j : Nat} (ha : W 34 = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = BitVec.ofNat 64 d)
    (h10 : u.gpr .r10 = BitVec.ofNat 64 j) (ha' : a < 2 ^ 64) (hj1 : 1 ≤ j) (hj' : j < 2 ^ 64) :
    WP isa (.block nextPass) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx, .r10] u u' ∧
      u'.gpr .rdx = BitVec.ofNat 64 (2 * d) ∧ u'.gpr .r10 = BitVec.ofNat 64 (j - 1) ∧
      u'.zf = some (decide (j - 1 = 0)) ∧ Rep u'.mem F S V (upd W 34 (BitVec.ofNat 64 (a / 2))) := by
  have G' := L.geo
  rw [nextPass_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F (8 * 34)) (BitVec.ofNat 64 (a / 2)))
    ?_ rfl) fun u1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sA) (by decide), L.st (d := sA) (by decide),
      R.slot (d := sA) (k := 34) rfl (by decide) ha, shr1_ofNat ha']
    rfl
  have R1 : Rep u1.mem F S V _ := hm1 ▸ R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 (a / 2))
  have L1 := L.of_rep' R R1 (by simp [upd]) (k1.gpr (by decide)) k1.2.2
  have hdx1 : u1.gpr .rdx = BitVec.ofNat 64 d := (k1.gpr (by decide)).trans hdx
  have h101 : u1.gpr .r10 = BitVec.ofNat 64 j := (k1.gpr (by decide)).trans h10
  refine WP.mono (WP.keep [.rdx, .r10] (Q := fun u' => u'.gpr .rdx = BitVec.ofNat 64 (2 * d) ∧
    u'.gpr .r10 = BitVec.ofNat 64 (j - 1) ∧ u'.zf = some (decide (j - 1 = 0)) ∧ u'.mem = u1.mem) ?_ rfl)
    fun u2 ⟨⟨hd2, h102, hz, hm2⟩, k2⟩ => ?_
  · xrun [hdx1, h101, dbl_ofNat, sub1_ofNat hj1, ofNat_beq_zero (show j - 1 < 2 ^ 64 by omega)]
  exact ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), (k1.trans k2).mono (by decide), hd2, h102, hz,
    hm2 ▸ R1⟩

/-- The buffer before the shift, as a function of the index: its first 1024
bytes, and zeros after them. -/
def bufB (V : Nat → Byte) (x : Nat) : Byte := if x < 1024 then V (oBuf + x) else 0

/-- Before pass `p` of the shift by `A`. -/
structure ShiftI (u₀ : State) (F S : Addr) (V₀ : Nat → Byte) (W₀ : Nat → BitVec 64) (A p : Nat) (w : State) :
    Prop where
  L : Lay w F S
  keep : Keep [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] u₀ w
  rcx : w.gpr .rcx = off S oBuf
  rdx : w.gpr .rdx = BitVec.ofNat 64 (2 ^ p)
  r10 : w.gpr .r10 = BitVec.ofNat 64 (10 - p)
  rep : ∃ V W, Rep w.mem F S V W ∧ W 34 = BitVec.ofNat 64 (A / 2 ^ p) ∧ (∀ k < nW, k ≠ 34 → W k = W₀ k) ∧
    (∀ i < 2048, V (oBuf + i) = bufB V₀ (i + A % 2 ^ p)) ∧
    (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + 2048) → V o = V₀ o)

theorem add1_ofNat (a : Nat) : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := (BitVec.ofNat_add a 1).symm

/-- The buffer shifted left by `idx + 1` bytes, in 10 passes. -/
theorem shift_ok {u : State} {F S : Addr} (L : Lay u F S) {V₀ : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V₀ W) (hcx : u.gpr .rcx = off S oBuf) {idx : Nat} (hi : W 32 = BitVec.ofNat 64 idx)
    (hA : idx + 1 < 1024) (hz : ∀ x, 1024 ≤ x → x < 2048 → V₀ (oBuf + x) = 0) :
    WP isa shift u fun u' => Lay u' F S ∧ Keep [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] u u' ∧
      ∃ V W', Rep u'.mem F S V W' ∧ (∀ k < nW, k ≠ 34 → k ≠ 35 → k ≠ 36 → W' k = W k) ∧
        (∀ i < 2048, V (oBuf + i) = bufB V₀ (i + (idx + 1))) ∧
        (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + 2048) → V o = V₀ o) := by
  have G' := L.geo
  have c3 : oBuf = 1024 := rfl
  unfold shift
  have R1 := R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 (idx + 1))
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .r10] (Q := fun v =>
      v.gpr .rdx = BitVec.ofNat 64 1 ∧ v.gpr .r10 = BitVec.ofNat 64 10 ∧
      v.mem = u.mem.writeW (off F (8 * 34)) (BitVec.ofNat 64 (idx + 1))) ?_ rfl) fun v ⟨⟨hdv, h10v, hm⟩, hk⟩ => ?_)
  · xrun [ea_sp, L.rsp, L.ld (d := sIdx) (by decide), L.st (d := sA) (by decide),
      R.slot (d := sIdx) (k := 32) rfl (by decide) hi, add1_ofNat]
    all_goals rfl
  have hcv : v.gpr .rcx = off S oBuf := (hk.gpr (by decide)).trans hcx
  have Rv : Rep v.mem F S V₀ _ := hm ▸ R1
  have Lv := L.of_rep' R Rv (by simp [upd]) (hk.gpr (by decide)) hk.2.2
  have I0 : ShiftI u F S V₀ W (idx + 1) 0 v := ⟨Lv, hk.mono (by decide), hcv, hdv, h10v, V₀, _, Rv, by simp [upd],
    fun k _ h1 => by simp only [upd, ifn h1],
    fun i hi => by
      simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, bufB]
      by_cases h : i < 1024
      · rw [ifp h]
      · rw [ifn h, hz i (by omega) hi], fun _ _ => rfl⟩
  refine WP.loop (M := isa) (fun n w => ∃ p, n = 10 - p ∧ p < 10 ∧ ShiftI u F S V₀ W (idx + 1) p w)
    ?_ (10 - 0) v ⟨0, rfl, by decide, I0⟩
  rintro n w ⟨p, rfl, hp, I⟩
  obtain ⟨V, W', Rw, h34, hW, hB, hO⟩ := I.rep
  have hp9 : 2 ^ p ≤ 512 := Nat.le_trans (Nat.pow_le_pow_right (by decide) (show p ≤ 9 by omega))
    (by decide : 2 ^ 9 ≤ 512)
  have hp0 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hAp : idx + 1 < 2 ^ 64 := by omega
  refine WP.seq (WP.mono (shiftPass_ok I.L Rw I.rcx I.rdx hp0 (by omega)) fun w1 ⟨L1, k1, R1⟩ => ?_)
  refine WP.mono (nextPass_ok L1 R1 (a := (idx + 1) / 2 ^ p) (d := 2 ^ p) (j := 10 - p) h34
    ((k1.gpr (by decide)).trans I.rdx) ((k1.gpr (by decide)).trans I.r10)
    (by have := Nat.div_le_self (idx + 1) (2 ^ p); omega) (by omega) (by omega))
    fun w2 ⟨L2, k2, hd2, h102, hz2, R2⟩ => ?_
  have hbit : (W' 34).toNat % 2 = (idx + 1) / 2 ^ p % 2 := by
    have := Nat.div_le_self (idx + 1) (2 ^ p)
    rw [h34, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (idx + 1) / 2 ^ p) (by omega)]
  have I' : ShiftI u F S V₀ W (idx + 1) (p + 1) w2 := by
    refine ⟨L2, ((I.keep.trans k1).trans k2).mono (by decide),
      ((k2.gpr (by decide)).trans (k1.gpr (by decide))).trans I.rcx,
      by rw [hd2, Nat.pow_succ, Nat.mul_comm], by rw [h102]; congr 1, _, _, R2, ?_, fun k hk h1 => ?_,
      fun i hi => ?_, fun o ho => ?_⟩
    · simp only [upd]; rw [Nat.pow_succ, Nat.div_div_eq_div_mul]; rfl
    · simp only [upd, ifn h1]; exact hW k hk h1
    · simp only [selV]
      rw [Nat.mod_pow_succ]
      by_cases hi' : i < 1024
      · rw [ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024 by omega)]
        rcases Nat.mod_two_eq_zero_or_one ((idx + 1) / 2 ^ p) with h0 | h1
        · rw [hbit, h0, show decide (0 = 1) = false from rfl]
          simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero]
          exact hB i hi
        · rw [hbit, h1, show decide (1 = 1) = true from rfl]
          simp only [ite_true, Nat.mul_one]
          rw [show oBuf + i + 2 ^ p = oBuf + (i + 2 ^ p) by omega, hB (i + 2 ^ p) (by omega)]
          congr 1; omega
      · rw [ifn (show ¬ (oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + 1024) by omega), hB i hi, bufB, bufB,
          ifn (show ¬ (i + (idx + 1) % 2 ^ p < 1024) by omega),
          ifn (show ¬ (i + ((idx + 1) % 2 ^ p + 2 ^ p * ((idx + 1) / 2 ^ p % 2)) < 1024) by omega)]
    · have ho' : ¬ (oBuf ≤ o ∧ o < oBuf + 1024) := fun h => ho ⟨h.1, by omega⟩
      unfold selV; rw [ifn ho']; exact hO o ho
  by_cases hl : p + 1 < 10
  · refine .inr ⟨by simp only [eval, hz2]; simp; omega, 10 - (p + 1), by omega, p + 1, rfl, hl, I'⟩
  · have hp10 : p + 1 = 10 := by omega
    refine .inl ⟨by simp only [eval, hz2]; simp; omega, I'.L, I'.keep, ?_⟩
    obtain ⟨V', W'', R', _, hW', hB', hO'⟩ := I'.rep
    refine ⟨V', W'', R', fun k hk h1 _ _ => hW' k hk h1, fun i hi => ?_, hO'⟩
    rw [hB' i hi, hp10, Nat.mod_eq_of_lt (show idx + 1 < 2 ^ 10 by omega)]

end VG.Proof.RsaOaep.X86_64
