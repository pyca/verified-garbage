import VerifiedGarbage.Proof.RsaOaep.X86_64.Label

/-!
# RSAES-OAEP encryption on x86-64: `EM` before masking

The pieces of `encEm`: `EM`'s place cleared (`clearEm_ok`), the seed
copied to `EM + 1` (`copySeed_ok`), the label's hash copied to
`EM + 1 + hLen` (`copyLh_ok`), and `0x01` and the message placed at the end
of `EM` (`putMsg_ok`); and MGF1's slots for masking `DB` and the seed
(`dbArgs_ok`, `seedArgs_ok`), which decryption uses too.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum.X86_64 (off word Scr off_off)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

theorem clearEm_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) :
    WP isa clearEm u fun u' => Lay u' F S ∧ Keep [.rcx, .rax, .r8] u u' ∧ Rep u'.mem F S (clrV V oEm 1024) W := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8] (Q := fun v => v.gpr .rcx = off S oEm ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk⟩ => ?_)
  · xrun [clearEm, scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (clearQ_ok Lv (hm ▸ R) (o := oEm) (n := 1024) (by decide) (by decide) (by decide) (by decide)
    h₁ h₂ h₃) fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), Rw⟩

/-- A copy into our working space from `rsi = p`, set by `pre`. -/
theorem copyFrom_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pre : List Instr} {p : Addr} {o disp n : Nat}
    (hpre : WP isa (.block pre) u fun v => v.gpr .rsi = p ∧ v.gpr .rcx = off S o ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem ∧ Keep [.rsi, .rcx, .r8] u v)
    (hn : 0 < n) (hn31 : n < 2 ^ 31) (ho : o + disp + n ≤ oRsa)
    (hsrc : ∀ i < n, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < n, ∀ j < n, p + BitVec.ofNat 64 i ≠ off S (o + disp + j)) :
    WP isa (.seq (.block pre) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 disp) .rax]
      (.imm (BitVec.ofNat 32 n)))) u fun u' => Lay u' F S ∧ Keep [.rsi, .rcx, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) (o + disp) n) W := by
  refine WP.seq (WP.mono hpre fun v ⟨h₁, h₂, h₃, hm, hk⟩ => ?_)
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have hsrc' : ∀ i < n, InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [hk.2.1, hk.2.2]; exact hsrc i hi
  refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (stepI_ok hn31 v [.rax, .r8]) hn ho h₁ h₂ h₃
    hsrc' hdis) fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk.trans kw).mono (by decide), ?_⟩
  rw [hm] at Rw; exact Rw

theorem copySeed_ok {H : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {p : Addr} (hp : W 31 = p) (hD : 0 < H.D) (hD64 : H.D ≤ 64)
    (hsrc : ∀ i < H.D, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < H.D, ∀ j < H.D, p + BitVec.ofNat 64 i ≠ off S (oEm + (oEm + 1) + j)) :
    WP isa (copySeed H) u fun u' => Lay u' F S ∧ Keep [.rsi, .rcx, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (p + BitVec.ofNat 64 i)) (oEm + (oEm + 1)) H.D) W := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  refine copyFrom_ok L R ?_ hD (by omega) (by unfold oEm oRsa; omega) hsrc hdis
  refine WP.mono (WP.keep [.rsi, .rcx, .r8] (Q := fun v => v.gpr .rsi = p ∧ v.gpr .rcx = off S oEm ∧
    v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩
  xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sSeed) (by decide), hs,
    R.slot (d := sSeed) (k := 31) rfl (by decide) hp, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide)]

theorem copyLh_ok {H : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hD : 0 < H.D) (hD64 : H.D ≤ 64) :
    WP isa (copyLh H) u fun u' => Lay u' F S ∧ Keep [.rsi, .rcx, .rax, .r8] u u' ∧
      Rep u'.mem F S (cpV V (fun i => V (oDig + i)) (oEm + (oEm + 1 + H.D)) H.D) W := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have c1 : oDig = 3328 := rfl
  have c2 : oEm = 0 := rfl
  refine WP.mono (copyFrom_ok L R (p := off S oDig) (o := oEm) ?_ hD (by omega) (by unfold oRsa; omega)
    (fun i hi => by rw [off_plus]; exact L.sld8 (by unfold oRsa; omega))
    (fun i hi j hj => by rw [off_plus]; exact Offset.add_ofNat_ne S (by omega) (by omega) (by omega)))
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, kw, ?_⟩
  · refine WP.mono (WP.keep [.rsi, .rcx, .r8] (Q := fun v => v.gpr .rsi = off S oDig ∧ v.gpr .rcx = off S oEm ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, c, d, k⟩
    xrun [copyLh, scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), hs, VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]
  · refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
    simp only [cpV]
    split
    · rw [off_plus, R.scr _ (by unfold oRsa; omega)]
    · rfl

theorem cpV_zero (V src : Nat → Byte) (o : Nat) : cpV V src o 0 = V := by
  funext x; simp only [cpV]; rw [ifn (by omega)]

theorem putMsg_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k mLen : Nat} {p : Addr} (hk : W 23 = BitVec.ofNat 64 k) (hml : W 30 = BitVec.ofNat 64 mLen)
    (hp : W 29 = p) (hfit : mLen + 1 ≤ k) (hk1 : k ≤ 1024)
    (hsrc : ∀ i < mLen, InRegions (u.rd ++ u.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < mLen, ∀ j ≤ mLen, p + BitVec.ofNat 64 i ≠ off S (k - mLen - 1 + j)) :
    WP isa putMsg u fun u' => Lay u' F S ∧ Keep [.rdi, .rax, .rsi, .r10, .r8] u u' ∧
      Rep u'.mem F S (cpV (upd V (k - mLen - 1) 1) (fun i => u.mem (p + BitVec.ofNat 64 i)) (k - mLen - 1 + 1) mLen)
        W := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have c2 : oEm = 0 := rfl
  have hst := L.sst8 (d := oEm + k - mLen - 1) (by unfold oEm oRsa; omega)
  have e0 : oEm + k - mLen - 1 = k - mLen - 1 := by unfold oEm; omega
  have G' := L.geo
  have R1 := R.wb G' (o := k - mLen - 1) (by unfold oRsa; omega) 1
  have hsplit : putMsg = .seq (.block ((scr .rdi oEm ++ [.alu .add .rdi (.mem (sp sK)),
      .alu .sub .rdi (.mem (sp sMsgLen)), .alu .sub .rdi (.imm 1), .mov32 .rax (.imm 1)]) ++
      [.store8 (at_ .rdi) .rax, .mov .rsi (.mem (sp sMsg)), .mov .r10 (.mem (sp sMsgLen)), .mov32 .r8 (.imm 0),
        .alu .test .r10 (.reg .r10)]))
      (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8 1) .rax] (.reg .r10))) := rfl
  rw [hsplit]
  refine WP.seq (WP.mono (WP.keep [.rdi, .rax, .rsi, .r10, .r8] (Q := fun v => v.gpr .rdi = off S (oEm + k - mLen - 1) ∧
      v.gpr .rsi = p ∧ v.gpr .r10 = BitVec.ofNat 64 mLen ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧
      v.zf = some (decide (mLen = 0)) ∧ v.mem = u.mem.writeW (off S (oEm + k - mLen - 1)) (1 : Byte)) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk'⟩ => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.rdi, .rax] (Q := fun v => v.gpr .rdi = off S (oEm + k - mLen - 1) ∧
      v.gpr .rax = 1 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨a, b, c⟩, kv⟩ => ?_
    · xrun [scr, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
        L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), L.ld (d := sMsgLen) (by decide), hs,
        R.slot (d := sK) (k := 23) rfl (by decide) hk, R.slot (d := sMsgLen) (k := 30) rfl (by decide) hml,
        VG.Proof.MlKem.X86_64.sx_ofNat (show oEm < 2 ^ 31 by decide), off_plus,
        off_sub _ (show mLen ≤ oEm + k by omega), off_sub1 _ (show 1 ≤ oEm + k - mLen by omega)]
    · have Lv : Lay v F S := L.congr (kv.gpr (by decide)) kv.2.2 (by rw [c])
      have Rv : Rep v.mem F S V W := c ▸ R
      have hst' := Lv.sst8 (d := oEm + k - mLen - 1) (by unfold oEm oRsa; omega)
      have R2 := R.wb L.geo (o := oEm + k - mLen - 1) (by unfold oEm oRsa; omega) (BitVec.setWidth 8 (1 : BitVec 64))
      xrun [ea_sp, ea_at0, Lv.rsp, a, b, hst', Lv.ld (d := sMsgLen) (by decide), Lv.ld (d := sMsg) (by decide),
        R2.slot (d := sMsgLen) (k := 30) rfl (by decide) hml, R2.slot (d := sMsg) (k := 29) rfl (by decide) hp, c,
        BitVec.and_self, ofNat_beq_zero (show mLen < 2 ^ 64 by omega)]
      rfl
  rw [e0] at h₁ hm
  have R1 := R.wb G' (o := k - mLen - 1) (by unfold oRsa; omega) (1 : Byte)
  have Lv : Lay v F S := L.of_rep R (hm ▸ R1) (hk'.gpr (by decide)) hk'.2.2
  have Rv : Rep v.mem F S (upd V (k - mLen - 1) 1) W := hm ▸ R1
  refine WP.ite (M := isa) _ (show isa.eval .e v = _ from h₅) (fun hz => ?_) (fun hz => ?_)
  · rw [decide_eq_true_eq] at hz; subst hz
    refine WP.mono (WP.keep [] (Q := fun w => w = v) (by xrun) rfl) fun w ⟨hw, _⟩ => ?_
    subst hw; exact ⟨Lv, hk'.mono (by decide), by rw [cpV_zero]; exact Rv⟩
  · rw [decide_eq_false_iff_not] at hz
    have hsrc' : ∀ i < mLen, InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 i) 1 := fun i hi => by
      rw [hk'.2.1, hk'.2.2]; exact hsrc i hi
    have hsame : ∀ i < mLen, v.mem (p + BitVec.ofNat 64 i) = u.mem (p + BitVec.ofNat 64 i) := fun i hi => by
      rw [hm, VG.WriteBytes.writeW8_apply, ifn (by have := hdis i hi 0 (by omega); rwa [Nat.add_zero] at this)]
    refine WP.mono (copy_ok Lv Rv (d := .rdi) (by decide) (o := k - mLen - 1) (disp := 1)
      (stepR_ok (by omega) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₃) (by omega)
      (by unfold oRsa; omega) h₂ h₁ h₄ hsrc'
      (fun i hi j hj => by have := hdis i hi (1 + j) (by omega); rwa [← Nat.add_assoc] at this))
      fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk'.trans kw).mono (by decide), ?_⟩
    refine (congrArg (fun V' => Rep w.mem F S V' W) (funext fun x => ?_)).mp Rw
    simp only [cpV]
    split
    · rw [hsame _ (by omega)]
    · rfl


/-! ## MGF1's slots -/

/-- MGF1's slots set to `src`, `srcLen`, `dst`, `dstLen`, the others kept. -/
def mW (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd W 17 (off S dst)) 18 (BitVec.ofNat 64 dstLen)) 15 (off S src)) 16 (BitVec.ofNat 64 srcLen)

theorem mW_args (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) :
    MArgs (mW W S src srcLen dst dstLen) S src srcLen dst dstLen :=
  ⟨by simp [mW, upd], by simp [mW, upd], by simp [mW, upd], by simp [mW, upd]⟩

theorem mW_other {W : Nat → BitVec 64} {S : Addr} {src srcLen dst dstLen k : Nat} (h1 : k < 15 ∨ 18 < k) :
    mW W S src srcLen dst dstLen k = W k := by
  simp only [mW, upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega), ifn (by omega)]

theorem dbArgs_ok {H : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hD : H.D < 2 ^ 30) (hkD : H.D + 1 ≤ k) :
    WP isa (.block (dbArgs H)) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx, .rcx, .r9] u u' ∧
      Rep u'.mem F S V (mW W S (oEm + 1) H.D (oEm + 1 + H.D) (k - (H.D + 1))) := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have G' := L.geo
  have R1 := (((R.wf G' (k := 17) (by decide) (off S (oEm + 1 + H.D))).wf G' (k := 18) (by decide)
    (BitVec.ofNat 64 (k - (H.D + 1)))).wf G' (k := 15) (by decide) (off S (oEm + 1))).wf G' (k := 16) (by decide)
    (BitVec.ofNat 64 H.D)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r9] (Q := fun u' => u'.mem =
      (((u.mem.writeW (off F (8 * 17)) (off S (oEm + 1 + H.D))).writeW (off F (8 * 18))
        (BitVec.ofNat 64 (k - (H.D + 1)))).writeW (off F (8 * 15)) (off S (oEm + 1))).writeW (off F (8 * 16))
        (BitVec.ofNat 64 H.D)) ?_ rfl) fun u' ⟨hm, kk⟩ => ⟨?_, kk, by rw [hm]; exact R1⟩
  · xrun [dbArgs, scr, Impl.Mgf1.X86_64.scr, lay, im, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), hs, R.slot (d := sK) (k := 23) rfl (by decide) hk,
      L.st (d := sDst) (by decide), L.st (d := sDstLen) (by decide), L.st (d := sSrc) (by decide),
      L.st (d := sSrcLen) (by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 + H.D < 2 ^ 31 by unfold oEm; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 < 2 ^ 31 by unfold oEm; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show H.D + 1 < 2 ^ 31 by omega), zx32 (show H.D < 2 ^ 32 by omega),
      VG.Offset.ofNat_sub_ofNat (show H.D + 1 ≤ k by omega)]
    rfl
  · exact L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2

theorem seedArgs_ok {H : Stream} {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hD : H.D < 2 ^ 30) (hkD : H.D + 1 ≤ k) :
    WP isa (.block (seedArgs H)) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx, .rcx, .r9] u u' ∧
      Rep u'.mem F S V (mW W S (oEm + 1 + H.D) (k - (H.D + 1)) (oEm + 1) H.D) := by
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have G' := L.geo
  have R1 := (((R.wf G' (k := 17) (by decide) (off S (oEm + 1))).wf G' (k := 18) (by decide)
    (BitVec.ofNat 64 H.D)).wf G' (k := 15) (by decide) (off S (oEm + 1 + H.D))).wf G' (k := 16) (by decide)
    (BitVec.ofNat 64 (k - (H.D + 1)))
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r9] (Q := fun u' => u'.mem =
      (((u.mem.writeW (off F (8 * 17)) (off S (oEm + 1))).writeW (off F (8 * 18))
        (BitVec.ofNat 64 H.D)).writeW (off F (8 * 15)) (off S (oEm + 1 + H.D))).writeW (off F (8 * 16))
        (BitVec.ofNat 64 (k - (H.D + 1)))) ?_ rfl) fun u' ⟨hm, kk⟩ => ⟨?_, kk, by rw [hm]; exact R1⟩
  · xrun [seedArgs, scr, Impl.Mgf1.X86_64.scr, lay, im, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sK) (by decide), hs, R.slot (d := sK) (k := 23) rfl (by decide) hk,
      L.st (d := sDst) (by decide), L.st (d := sDstLen) (by decide), L.st (d := sSrc) (by decide),
      L.st (d := sSrcLen) (by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 + H.D < 2 ^ 31 by unfold oEm; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oEm + 1 < 2 ^ 31 by unfold oEm; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show H.D + 1 < 2 ^ 31 by omega), zx32 (show H.D < 2 ^ 32 by omega),
      VG.Offset.ofNat_sub_ofNat (show H.D + 1 ≤ k by omega)]
    rfl
  · exact L.of_rep' R (by rw [hm]; exact R1) (by simp [upd]) (kk.gpr (by decide)) kk.2.2

end VG.Proof.RsaOaep.X86_64
