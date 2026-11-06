module

import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Loops
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSAES-OAEP on x86-64: MGF1

The blocks of `mgfXor lay G`, which XORs `MGF1(src, dstLen)` into `dst`,
where `src` (`srcLen` bytes) and `dst` (`dstLen` bytes) are ranges of our working
space below the hash function's, given by MGF1's slots: for each counter
`c`, the state is set by `init`, `update` absorbs `src` and then
`I2OSP(c, 4)` (written to `scratch + oCtr`, `counter_ok`), `finalize`
writes the digest to `scratch + oDig`, and the first
`min(hLen, dstLen - c hLen)` bytes of the digest are XORed into
`dst + c hLen`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs round xorOut xorHead nextCtr initArgs updSrcArgs
  updCtrArgs finArgs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off word off_off)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)

/-! ## Where MGF1 works -/

/-- The ranges of our working space the hash functions' calls and MGF1's
counter write. -/
def hashR : List (Nat × Nat) := [(oSt, 256), (oDig, 64), (oCtr, 4), (oW, 2048)]

/-- Outside them. -/
def mOut (o : Nat) : Prop := ¬ inR hashR o

theorem mOut_iff (o : Nat) : mOut o ↔ o < oSt ∨ (oDig + 64 ≤ o ∧ o < oCtr) ∨ (oCtr + 4 ≤ o ∧ o < oW) ∨
    oW + 2048 ≤ o := by
  simp only [mOut, hashR, inR_cons, inR_nil, or_false, oSt, oDig, oCtr, oW]
  omega_using []

/-- `src` and `dst`, below the hash functions' ranges and apart. -/
structure MFit (src srcLen dst dstLen : Nat) : Prop where
  fs : src + srcLen ≤ oSt
  fd : dst + dstLen ≤ oSt
  sep : src + srcLen ≤ dst ∨ dst + dstLen ≤ src
  pos : 0 < dstLen
  dstB : dstLen ≤ 2048

/-- What MGF1's slots hold. -/
structure MArgs (W : Nat → BitVec 64) (S : Addr) (src srcLen dst dstLen : Nat) : Prop where
  hsrc : W 15 = off S src
  hsl : W 16 = BitVec.ofNat 64 srcLen
  hdst : W 17 = off S dst
  hdl : W 18 = BitVec.ofNat 64 dstLen

theorem MArgs.of_eq {W W' : Nat → BitVec 64} {S : Addr} {src srcLen dst dstLen : Nat}
    (h : MArgs W S src srcLen dst dstLen) (hW : ∀ k, 15 ≤ k → k ≤ 18 → W' k = W k) :
    MArgs W' S src srcLen dst dstLen :=
  ⟨(hW 15 (by omega_using []) (by omega_using [])).trans h.hsrc, (hW 16 (by omega_using []) (by omega_using [])).trans h.hsl,
    (hW 17 (by omega_using []) (by omega_using [])).trans h.hdst, (hW 18 (by omega_using []) (by omega_using [])).trans h.hdl⟩

/-- A slot, read through `Rep`. -/
theorem Rep.slot {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : W k = v) : m.readW (off F d) 64 = v := by
  rw [← hv, R.rd k hd hk]

variable {G : Stream} (hG : StreamOK G)

/-! ## The arguments of the calls -/

theorem updSrc_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {src srcLen dst dstLen : Nat} (A : MArgs W S src srcLen dst dstLen) :
    WP isa (.block (updSrcArgs lay)) u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 0 ∧
      u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧ u'.gpr .r8 = off S oW ∧ u'.mem = u.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 0 ∧ u'.gpr .rdx = off S src ∧ u'.gpr .rcx = BitVec.ofNat 64 srcLen ∧
      u'.gpr .r8 = off S oW ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e, f⟩, k⟩ => ⟨a, b, c, d, e, f, k⟩
  xrun [updSrcArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sSrc) (by decide), L.ld (d := sSrcLen) (by decide), hs,
    R.slot (d := sSrc) (k := 15) rfl (by decide) A.hsrc, R.slot (d := sSrcLen) (k := 16) rfl (by decide) A.hsl,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]

/-- `I2OSP(c, 4)` at `scratch + oCtr`. -/
def ctrV (V : Nat → Byte) (c : Nat) (x : Nat) : Byte :=
  if oCtr ≤ x ∧ x < oCtr + 4 then (Spec.Rsa.i2osp c 4).getD (x - oCtr) 0 else V x

theorem trunc_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem updCtr_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen c : Nat} (hl : W 16 = BitVec.ofNat 64 srcLen) (hc : W 19 = BitVec.ofNat 64 c)
    (hc32 : c < 2 ^ 32) :
    WP isa (.block (updCtrArgs lay)) u fun u' => Lay u' F S ∧ u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oCtr ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oW ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] u u' ∧ Rep u'.mem F S (ctrV V c) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  have G' := L.geo
  have R1 := (((R.wb G' (o := oCtr + 3) (by decide) (BitVec.ofNat 8 c)).wb G'
    (o := oCtr + 2) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8))).wb G'
    (o := oCtr + 1) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).wb G'
    (o := oCtr) (by decide) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .rax] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 srcLen ∧ u'.gpr .rdx = off S oCtr ∧ u'.gpr .rcx = BitVec.ofNat 64 4 ∧
      u'.gpr .r8 = off S oW ∧ u'.mem =
      (((u.mem.writeW (off S (oCtr + 3)) (BitVec.ofNat 8 c)).writeW (off S (oCtr + 2))
        (BitVec.ofNat 8 (c / 2 ^ 8))).writeW (off S (oCtr + 1)) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8))).writeW
        (off S oCtr) (BitVec.ofNat 8 (c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8))) ?_ rfl)
    fun u' ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ⟨?_, h₁, h₂, h₃, h₄, h₅, hk, hm ▸ ?_⟩
  · xrun [updCtrArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_at, ea_sp, L.rsp,
      L.ld (d := sScr) (by decide), L.ld (d := sCtr) (by decide), L.ld (d := sSrcLen) (by decide), hs,
      R.slot (d := sCtr) (k := 19) rfl (by decide) hc, off_off,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oCtr < 2 ^ 31 by decide),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide),
      L.sst8 (d := oCtr + 3) (by decide), L.sst8 (d := oCtr + 2) (by decide), L.sst8 (d := oCtr + 1) (by decide),
      L.sst8 (d := oCtr) (by decide), trunc_ofNat, shr_ofNat 8 (show c < 2 ^ 64 by omega_using [hc32]),
      shr_ofNat 8 (show c / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]), shr_ofNat 8 (show c / 2 ^ 8 / 2 ^ 8 < 2 ^ 64 by omega_using [hc32]),
      zx32 (show 4 < 2 ^ 32 by omega_using []), show off S oCtr + 0 = off S oCtr from BitVec.add_zero _]
    have w14 : W 14 = S := (R.rd 14 rfl (by decide)).symm.trans hs
    simp only [show S + BitVec.ofNat 64 oCtr = off S oCtr from rfl, R1.slot (d := sScr) (k := 14) rfl (by decide) w14,
      R1.slot (d := sSrcLen) (k := 16) rfl (by decide) hl]
    exact ⟨trivial, trivial, trivial⟩
  · exact L.congr (hk.gpr (by decide)) hk.2.2 (by
      rw [hm, slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R1.fr 14 (by decide), R.fr 14 (by decide)])
  · refine (congrArg (fun V' => Rep _ F S V' _) (funext fun x => ?_)).mp R1
    have e1 : c / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 3 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    have e2 : c / 2 ^ 8 / 2 ^ 8 = c / 256 ^ 2 := by rw [Nat.div_div_eq_div_mul]
    have e3 : c / 2 ^ 8 = c / 256 ^ 1 := rfl
    simp only [upd, ctrV, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases (show x = oCtr ∨ x = oCtr + 1 ∨ x = oCtr + 2 ∨ x = oCtr + 3 ∨
        ¬(oCtr ≤ x ∧ x < oCtr + 4) by omega_using []) with h | h | h | h | h
    · subst h; simp [e1]
    · subst h; simp [e2]
    · subst h; simp [e3]
    · subst h; simp
    · rw [ifn h, ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h]), ifn (by omega_using [h])]

theorem finA_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {srcLen : Nat} (hl : W 16 = BitVec.ofNat 64 srcLen) :
    WP isa (.block (finArgs lay)) u fun u' => u'.gpr .rdi = off S oSt ∧ u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧
      u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oW ∧ u'.mem = u.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx] u u' := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx] (Q := fun u' => u'.gpr .rdi = off S oSt ∧
      u'.gpr .rsi = BitVec.ofNat 64 (srcLen + 4) ∧ u'.gpr .rdx = off S oDig ∧ u'.gpr .rcx = off S oW ∧
      u'.mem = u.mem) ?_ rfl) fun u' ⟨⟨a, b, c, d, e⟩, k⟩ => ⟨a, b, c, d, e, k⟩
  xrun [finArgs, Impl.Mgf1.X86_64.scr, lay, List.cons_append, List.nil_append, ea_sp, L.rsp,
    L.ld (d := sScr) (by decide), L.ld (d := sSrcLen) (by decide), hs,
    R.slot (d := sSrcLen) (k := 16) rfl (by decide) hl, ofNat_add_lit,
    VG.Proof.MlKem.X86_64.sx_ofNat (show oSt < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide),
    VG.Proof.MlKem.X86_64.sx_ofNat (show oW < 2 ^ 31 by decide)]



/-! ## One counter -/

/-- The view of memory after a call, as a function of its own. -/
theorem Rep.ex {m : Mem} {F S : Addr} {p : Nat → Prop} [DecidablePred p] {f V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep m F S (fun o => if p o then f o else V o) W) :
    ∃ V', Rep m F S V' W ∧ (∀ o, ¬ p o → V' o = V o) ∧ (∀ o, p o → V' o = f o) :=
  ⟨_, R, fun _ h => ifn h _ _, fun _ h => ifp h _ _⟩

theorem repr_congr {R : Mem → Addr → List Byte → Prop} {m : Mem} {p : Addr} {a b : List Byte} (h : a = b)
    (hr : R m p a) : R m p b := h ▸ hr

/-- The loop's invariant after `c` counters. -/
structure MgfI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (mk : List Byte)
    (dst dstLen D c : Nat) (v : State) : Prop where
  L : Lay v F S
  rd : v.rd = u₀.rd
  wr : v.wr = u₀.wr
  cs : ∀ r ∈ calleeSaved, v.gpr r = u₀.gpr r
  rep : ∃ V' W', Rep v.mem F S V' W' ∧ W' 19 = BitVec.ofNat 64 c ∧ W' 20 = BitVec.ofNat 64 (c * D) ∧
    (∀ k < nW, k ≠ 19 → k ≠ 20 → W' k = W k) ∧
    ∀ o < oRsa, mOut o → V' o = mixV V mk dst (min (c * D) dstLen) o

theorem keep_cs' {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : ∀ r ∈ calleeSaved, r ∉ rs) : ∀ r ∈ calleeSaved, v.gpr r = u.gpr r :=
  fun r hr => k.gpr (h r hr)

theorem cs_disj (rs : List Reg) (h : rs.all (fun r => !calleeSaved.contains r) = true) :
    ∀ r ∈ calleeSaved, r ∉ rs := fun r hr hr' => by
  have := List.all_eq_true.mp h r hr'
  simp only [Bool.not_eq_true'] at this
  simp_all

/-! ## MGF1 -/

/-- The counter and `done` set to 0: the loop's invariant for counter 0. -/
theorem mgfHead_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (mk : List Byte) (dst dstLen : Nat) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp lay.sCtr) .rax, .store (sp lay.sDone) .rax]) u
      (MgfI u F S V W mk dst dstLen G.D 0) := by
  have G' := L.geo
  have R2 := (R.wf G' (k := 19) (by decide) 0#64).wf G' (k := 20) (by decide) 0#64
  rw [show off F (8 * 19) = off F sCtr from rfl, show off F (8 * 20) = off F sDone from rfl] at R2
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem =
      (u.mem.writeW (off F sCtr) 0#64).writeW (off F sDone) 0#64) ?_ rfl) fun v ⟨hm, hk⟩ => ?_
  · xrun [lay, ea_sp, L.rsp, L.st (d := sCtr) (by decide), L.st (d := sDone) (by decide),
      show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl]
  have R2' : Rep v.mem F S V (upd (upd W 19 0#64) 20 0#64) := hm ▸ R2
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by
    rw [slot_eq sScr 14 rfl, slot_eq sScr 14 rfl, R2'.fr 14 (by decide), R.fr 14 (by decide)]; simp [upd])
  exact ⟨Lv, hk.2.1, hk.2.2, keep_cs' hk (cs_disj _ (by decide)), _, _, R2', by simp [upd], by simp [upd],
    fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1],
    fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_using [])]⟩

end VG.Proof.RsaOaep.X86_64
