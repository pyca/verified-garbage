module

import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `RsaOaep.X86_64.Loops`, which this module and modules that import it used -/

section

/-!
# RSAES-OAEP on x86-64: the loops that clear, copy and XOR bytes

The counter of a byte loop (`step`, with an immediate or a register as its
end: `stepI_ok`, `stepR_ok`), clearing a range of our working space a word
at a time (`clearQ_ok`), and copying bytes into it (`copy_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_add_one ofNat_sub_beq wp_upto)

/-! ## Counters -/

/-- What the counter of a loop over `n` iterations does, from a state `u₀`
whose registers the loop keeps but `rs` (and `r8`). -/
def StepOk (cnt : Src) (n : Nat) (u₀ : State) (rs : List Reg) : Prop :=
  ∀ j < n, ∀ u : State, Keep rs u₀ u → u.gpr .r8 = BitVec.ofNat 64 j →
    WP isa (.block (step cnt)) u fun u' => u'.zf = some (decide (j + 1 = n)) ∧
      u'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧ u'.mem = u.mem ∧ Keep [.r8] u u'

theorem stepI_ok {n : Nat} (hn : n < 2 ^ 31) (u₀ : State) (rs : List Reg) :
    StepOk (.imm (BitVec.ofNat 32 n)) n u₀ rs := fun j hj u _ h8 => by
  refine WP.mono (WP.keep [.r8] (Q := fun u' => u'.zf = some (decide (j + 1 = n)) ∧
    u'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [step, h8, ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat hn,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_using [hn, hj]) (show n < 2 ^ 64 by omega_using [hn])]

theorem stepR_ok {r : Reg} {n : Nat} (hn : n < 2 ^ 63) (u₀ : State) {rs : List Reg} (hr : r ∉ rs) (hr8 : r ≠ .r8)
    (h : u₀.gpr r = BitVec.ofNat 64 n) : StepOk (.reg r) n u₀ rs := fun j hj u hk h8 => by
  have hu : u.gpr r = BitVec.ofNat 64 n := (hk.gpr hr).trans h
  refine WP.mono (WP.keep [.r8] (Q := fun u' => u'.zf = some (decide (j + 1 = n)) ∧
    u'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [step, h8, ofNat_add_lit, hr8, hu,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_using [hn, hj]) (show n < 2 ^ 64 by omega_using [hn])]

/-- A byte loop, from a body that keeps the counter. -/
theorem byteLoop_ok {body : List Instr} {cnt : Src} {n : Nat} (hn : 0 < n) {u₀ : State} {rs : List Reg}
    (hs : StepOk cnt n u₀ rs) (I : Nat → State → Prop)
    (hb : ∀ j < n, ∀ u, I j u → WP isa (.block body) u fun u' => Keep rs u₀ u' ∧
      u'.gpr .r8 = BitVec.ofNat 64 j ∧
      ∀ u'', Keep [.r8] u' u'' → u''.mem = u'.mem → u''.gpr .r8 = BitVec.ofNat 64 (j + 1) → I (j + 1) u'')
    {u : State} (h0 : I 0 u) : WP isa (byteLoop body cnt) u (I n) :=
  wp_upto (a := 0) (N := n) hn I (fun j _ hj v hv => by
    rw [WP.block_append_iff]
    exact WP.mono (hb j hj v hv) fun v' ⟨hk, h8, hnext⟩ =>
      WP.mono (hs j hj v' hk h8) fun v'' ⟨hz, h8', hm, hk'⟩ => ⟨hz, hnext v'' hk' hm h8'⟩) (fun _ h => h) h0

/-! ## Clearing words -/

/-- `n` bytes from `o` cleared. -/
def clrV (V : Nat → Byte) (o n : Nat) (x : Nat) : Byte := if o ≤ x ∧ x < o + n then 0 else V x

theorem clearQ_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o n : Nat} (hn : 0 < n) (h8 : n % 8 = 0) (ho : o + n ≤ oRsa) (hn31 : n < 2 ^ 31)
    (hcx : u.gpr .rcx = off S o) (hax : u.gpr .rax = 0) (hr8 : u.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8),
        .alu .cmp .r8 (.imm (BitVec.ofNat 32 n))]) .ne) u fun u' =>
      Lay u' F S ∧ Keep [.r8] u u' ∧ Rep u'.mem F S (clrV V o n) W := by
  refine wp_upto (a := 0) (N := n / 8) (by omega_using [hn, h8]) (fun j v => Lay v F S ∧ Keep [.r8] u v ∧
      v.gpr .r8 = BitVec.ofNat 64 (8 * j) ∧ Rep v.mem F S (clrV V o (8 * j)) W) ?_ (fun v ⟨Lv, k, _, Rv⟩ => ?_)
    ⟨L, Keep.refl _ _, hr8, (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
      simp only [clrV]; rw [ifn (by omega_using [])])).mpr R⟩
  · intro j _ hj v ⟨Lv, k, hv8, Rv⟩
    have hea : v.ea (ix .rcx .r8) = off S (o + 8 * j) := by
      rw [ea_ix0, k.gpr (by decide), hcx, hv8]; exact off_off S o (8 * j)
    refine WP.mono (WP.keep [.r8] (Q := fun v' => v'.zf = some (decide (j + 1 = n / 8)) ∧
        v'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧ v'.mem = v.mem.writeW (off S (o + 8 * j)) (0#64)) ?_ rfl)
      fun v' ⟨⟨hz, h8', hm⟩, k'⟩ => ⟨hz, ?_⟩
    · xrun [hea, Lv.sst (d := o + 8 * j) (by omega_using [ho, hj]), k.gpr (show Reg.rax ∉ [Reg.r8] by decide), hax, hv8,
        ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat hn31,
        ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega_using [hn31, hj]) (show n < 2 ^ 64 by omega_using [hn31])]
      exact ⟨by simp only [decide_eq_decide]; omega_using [h8], by congr 1, rfl⟩
    · have R' := Rv.ws Lv.geo (o := o + 8 * j) (w := 64) (by omega_using [ho, hj]) (0#64)
      rw [← hm] at R'
      have R'' : Rep v'.mem F S (clrV V o (8 * (j + 1))) W := by
        refine (congrArg (fun V' => Rep v'.mem F S V' W) (funext fun x => ?_)).mp R'
        simp only [stBytes, clrV]
        by_cases h1 : o + 8 * j ≤ x ∧ x < o + 8 * j + 64 / 8
        · rw [ifp h1, ifp (by omega_using [h1])]
          exact BitVec.eq_of_toNat_eq (by simp)
        · rw [ifn h1]
          by_cases h2 : o ≤ x ∧ x < o + 8 * j
          · rw [ifp h2, ifp (by omega_using [h2])]
          · rw [ifn h2, ifn (by omega_using [h1, h2])]
      exact ⟨Lv.of_rep Rv R'' (k'.gpr (by decide)) k'.2.2, (k.trans k').mono (by decide), h8', R''⟩
  · rw [show 8 * (n / 8) = n by omega_using [h8]] at Rv
    exact ⟨Lv, k, Rv⟩

/-! ## Copying bytes -/

/-- `n` bytes of `src` copied to `o`, over the first `j`. -/
def cpV (V : Nat → Byte) (src : Nat → Byte) (o j : Nat) (x : Nat) : Byte :=
  if o ≤ x ∧ x < o + j then src (x - o) else V x

structure CpI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (p : Addr) (o n j : Nat)
    (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (cpV V (fun i => u₀.mem (p + BitVec.ofNat 64 i)) o j) W
  src : ∀ i < n, v.mem (p + BitVec.ofNat 64 i) = u₀.mem (p + BitVec.ofNat 64 i)

/-- `n` bytes from `p` (`rsi`) copied to `scratch + o + disp`, `o` in `d`. -/
theorem copy_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {d : Reg} (hd : d ∉ [Reg.rax, .r8]) {p : Addr} {o disp n : Nat} {cnt : Src}
    (hs : StepOk cnt n u₀ [.rax, .r8]) (hn : 0 < n) (ho : o + disp + n ≤ oRsa)
    (hsi : u₀.gpr .rsi = p) (hdg : u₀.gpr d = off S o) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0)
    (hsrc : ∀ i < n, InRegions (u₀.rd ++ u₀.wr) (p + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < n, ∀ j < n, p + BitVec.ofNat 64 i ≠ off S (o + disp + j)) :
    WP isa (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix d .r8 disp) .rax] cnt) u₀ fun u' =>
      Lay u' F S ∧ Keep [.rax, .r8] u₀ u' ∧
      Rep u'.mem F S (cpV V (fun i => u₀.mem (p + BitVec.ofNat 64 i)) (o + disp) n) W := by
  refine WP.mono (byteLoop_ok hn hs (CpI u₀ F S V W p (o + disp) n) ?_ (u := u₀)
    ⟨L, Keep.refl _ _, h8, (congrArg (fun V' => Rep u₀.mem F S V' W) (funext fun x => by
      simp only [cpV]; rw [ifn (by omega_using [])])).mpr R, fun _ _ => rfl⟩) fun u' I => ⟨I.L, I.keep, I.R⟩
  intro j hj v I
  have hsv : v.gpr .rsi = p := (I.keep.gpr (by decide)).trans hsi
  have hdv : v.gpr d = off S o := (I.keep.gpr hd).trans hdg
  have hea₁ : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 j := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hea₂ : off S o + BitVec.ofNat 64 j + BitVec.ofNat 64 disp = off S (o + disp + j) := by
    rw [off_ix, off_off]; congr 1; omega_using []
  have hld : InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 j) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hsrc j hj
  have hst := I.L.sst8 (d := o + disp + j) (by omega_using [ho, hj])
  have hdr : d ≠ .rax := fun h => hd (by simp [h])
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (off S (o + disp + j)) (v.mem (p + BitVec.ofNat 64 j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hsv, I.r8, hea₁, hld, hdr, hdv, hea₂, hst, trunc_zext]
  · have R' := I.R.wb I.L.geo (o := o + disp + j) (by omega_using [ho, hj]) (v.mem (p + BitVec.ofNat 64 j))
    rw [← hm, ← hm'] at R'
    rw [I.src j hj] at R'
    have R'' : Rep v''.mem F S (cpV V (fun i => u₀.mem (p + BitVec.ofNat 64 i)) (o + disp) (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, cpV]
      by_cases hx : x = o + disp + j
      · subst hx; rw [ifp rfl, ifp (by omega_using []), show o + disp + j - (o + disp) = j by omega_using []]
      · rw [ifn hx]
        by_cases h' : o + disp ≤ x ∧ x < o + disp + j
        · rw [ifp h', ifp (by omega_using [h'])]
        · rw [ifn h', ifn (by omega_using [hx, h'])]
    refine ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R'', fun i hi => ?_⟩
    rw [hm', hm, VG.WriteBytes.writeW8_apply, ifn (hdis i hi j hj), I.src i hi]

/-! ## XORing bytes -/

/-- The `j` bytes at `b` XORed with those at `a`. -/
def xorV (V : Nat → Byte) (a b j : Nat) (x : Nat) : Byte :=
  if b ≤ x ∧ x < b + j then V x ^^^ V (a + (x - b)) else V x

theorem trunc_xor (x y : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = x ^^^ y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := y.toNat) (by omega_using [])]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.isLt y.isLt)

structure XorI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (a b j : Nat)
    (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.rax, .rdx, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (xorV V a b j) W

/-- The `n` bytes at `scratch + b` (`rdi`) XORed with those at
`scratch + a` (`rcx`), separate from them. -/
theorem xor_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {a b n : Nat} {cnt : Src}
    (hs : StepOk cnt n u₀ [.rax, .rdx, .r8]) (hn : 0 < n) (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa)
    (hab : a + n ≤ b ∨ b + n ≤ a)
    (hcx : u₀.gpr .rcx = off S a) (hdi : u₀.gpr .rdi = off S b) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rdx (.reg .rax),
        .store8 (ix .rdi .r8) .rdx] cnt) u₀ fun u' =>
      Lay u' F S ∧ Keep [.rax, .rdx, .r8] u₀ u' ∧ Rep u'.mem F S (xorV V a b n) W := by
  refine WP.mono (byteLoop_ok hn hs (XorI u₀ F S V W a b) ?_ (u := u₀)
    ⟨L, Keep.refl _ _, h8, (congrArg (fun V' => Rep u₀.mem F S V' W) (funext fun x => by
      simp only [xorV]; rw [ifn (by omega_using [])])).mpr R⟩) fun u' I => ⟨I.L, I.keep, I.R⟩
  intro j hj v I
  have hcv : v.gpr .rcx = off S a := (I.keep.gpr (by decide)).trans hcx
  have hdv : v.gpr .rdi = off S b := (I.keep.gpr (by decide)).trans hdi
  have z : BitVec.ofNat 64 0 = 0#64 := rfl
  have hea₁ : off S a + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (a + j) := by
    rw [z, BitVec.add_zero, off_plus]
  have hea₂ : off S b + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (b + j) := by
    rw [z, BitVec.add_zero, off_plus]
  have va : v.mem (off S (a + j)) = V (a + j) := by
    rw [I.R.scr _ (by omega_using [ha, hj]), xorV, ifn (by omega_using [hab, hj])]
  have vb : v.mem (off S (b + j)) = V (b + j) := by
    rw [I.R.scr _ (by omega_using [hb, hj]), xorV, ifn (by omega_using [])]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (off S (b + j)) (V (b + j) ^^^ V (a + j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hcv, hdv, I.r8, hea₁, hea₂, I.L.sld8 (d := a + j) (by omega_using [ha, hj]), I.L.sld8 (d := b + j) (by omega_using [hb, hj]),
      I.L.sst8 (d := b + j) (by omega_using [hb, hj]), va, vb, trunc_xor]
  · have R' := I.R.wb I.L.geo (o := b + j) (by omega_using [hb, hj]) (V (b + j) ^^^ V (a + j))
    rw [← hm, ← hm'] at R'
    have R'' : Rep v''.mem F S (xorV V a b (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, xorV]
      by_cases hx : x = b + j
      · subst hx; rw [ifp rfl, ifp (by omega_using []), Nat.add_sub_cancel_left]
      · rw [ifn hx]
        by_cases h' : b ≤ x ∧ x < b + j
        · rw [ifp h', ifp (by omega_using [h'])]
        · rw [ifn h', ifn (by omega_using [hx, h'])]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

end VG.Proof.RsaOaep.X86_64

end

end

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
