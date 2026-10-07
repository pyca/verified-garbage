import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

/-!
# RSAES-OAEP on x86-64: the loops that clear, copy and XOR bytes

The counter of a byte loop (`step`, with an immediate or a register as its
end: `stepI_ok`, `stepR_ok`), clearing a range of our working space a word
at a time (`clearQ_ok`), and copying bytes into it (`copy_ok`).
-/

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
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]

theorem stepR_ok {r : Reg} {n : Nat} (hn : n < 2 ^ 63) (u₀ : State) {rs : List Reg} (hr : r ∉ rs) (hr8 : r ≠ .r8)
    (h : u₀.gpr r = BitVec.ofNat 64 n) : StepOk (.reg r) n u₀ rs := fun j hj u hk h8 => by
  have hu : u.gpr r = BitVec.ofNat 64 n := (hk.gpr hr).trans h
  refine WP.mono (WP.keep [.r8] (Q := fun u' => u'.zf = some (decide (j + 1 = n)) ∧
    u'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧ u'.mem = u.mem) ?_ rfl) fun u' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [step, h8, ofNat_add_lit, hr8, hu,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]

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
  refine wp_upto (a := 0) (N := n / 8) (by omega) (fun j v => Lay v F S ∧ Keep [.r8] u v ∧
      v.gpr .r8 = BitVec.ofNat 64 (8 * j) ∧ Rep v.mem F S (clrV V o (8 * j)) W) ?_ (fun v ⟨Lv, k, _, Rv⟩ => ?_)
    ⟨L, Keep.refl _ _, hr8, (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
      simp only [clrV]; rw [ifn (by omega)])).mpr R⟩
  · intro j _ hj v ⟨Lv, k, hv8, Rv⟩
    have hea : v.ea (ix .rcx .r8) = off S (o + 8 * j) := by
      rw [ea_ix0, k.gpr (by decide), hcx, hv8]; exact off_off S o (8 * j)
    refine WP.mono (WP.keep [.r8] (Q := fun v' => v'.zf = some (decide (j + 1 = n / 8)) ∧
        v'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧ v'.mem = v.mem.writeW (off S (o + 8 * j)) (0#64)) ?_ rfl)
      fun v' ⟨⟨hz, h8', hm⟩, k'⟩ => ⟨hz, ?_⟩
    · xrun [hea, Lv.sst (d := o + 8 * j) (by omega), k.gpr (show Reg.rax ∉ [Reg.r8] by decide), hax, hv8,
        ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat hn31,
        ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]
      exact ⟨by simp only [decide_eq_decide]; omega, by congr 1, rfl⟩
    · have R' := Rv.ws Lv.geo (o := o + 8 * j) (w := 64) (by omega) (0#64)
      rw [← hm] at R'
      have R'' : Rep v'.mem F S (clrV V o (8 * (j + 1))) W := by
        refine (congrArg (fun V' => Rep v'.mem F S V' W) (funext fun x => ?_)).mp R'
        simp only [stBytes, clrV]
        by_cases h1 : o + 8 * j ≤ x ∧ x < o + 8 * j + 64 / 8
        · rw [ifp h1, ifp (by omega)]
          exact BitVec.eq_of_toNat_eq (by simp)
        · rw [ifn h1]
          by_cases h2 : o ≤ x ∧ x < o + 8 * j
          · rw [ifp h2, ifp (by omega)]
          · rw [ifn h2, ifn (by omega)]
      exact ⟨Lv.of_rep Rv R'' (k'.gpr (by decide)) k'.2.2, (k.trans k').mono (by decide), h8', R''⟩
  · rw [show 8 * (n / 8) = n by omega] at Rv
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
      simp only [cpV]; rw [ifn (by omega)])).mpr R, fun _ _ => rfl⟩) fun u' I => ⟨I.L, I.keep, I.R⟩
  intro j hj v I
  have hsv : v.gpr .rsi = p := (I.keep.gpr (by decide)).trans hsi
  have hdv : v.gpr d = off S o := (I.keep.gpr hd).trans hdg
  have hea₁ : p + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 j := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hea₂ : off S o + BitVec.ofNat 64 j + BitVec.ofNat 64 disp = off S (o + disp + j) := by
    rw [off_ix, off_off]; congr 1; omega
  have hld : InRegions (v.rd ++ v.wr) (p + BitVec.ofNat 64 j) 1 := by
    rw [I.keep.2.1, I.keep.2.2]; exact hsrc j hj
  have hst := I.L.sst8 (d := o + disp + j) (by omega)
  have hdr : d ≠ .rax := fun h => hd (by simp [h])
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (off S (o + disp + j)) (v.mem (p + BitVec.ofNat 64 j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hsv, I.r8, hea₁, hld, hdr, hdv, hea₂, hst, trunc_zext]
  · have R' := I.R.wb I.L.geo (o := o + disp + j) (by omega) (v.mem (p + BitVec.ofNat 64 j))
    rw [← hm, ← hm'] at R'
    rw [I.src j hj] at R'
    have R'' : Rep v''.mem F S (cpV V (fun i => u₀.mem (p + BitVec.ofNat 64 i)) (o + disp) (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, cpV]
      by_cases hx : x = o + disp + j
      · subst hx; rw [ifp rfl, ifp (by omega), show o + disp + j - (o + disp) = j by omega]
      · rw [ifn hx]
        by_cases h' : o + disp ≤ x ∧ x < o + disp + j
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
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
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
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
      simp only [xorV]; rw [ifn (by omega)])).mpr R⟩) fun u' I => ⟨I.L, I.keep, I.R⟩
  intro j hj v I
  have hcv : v.gpr .rcx = off S a := (I.keep.gpr (by decide)).trans hcx
  have hdv : v.gpr .rdi = off S b := (I.keep.gpr (by decide)).trans hdi
  have z : BitVec.ofNat 64 0 = 0#64 := rfl
  have hea₁ : off S a + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (a + j) := by
    rw [z, BitVec.add_zero, off_plus]
  have hea₂ : off S b + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (b + j) := by
    rw [z, BitVec.add_zero, off_plus]
  have va : v.mem (off S (a + j)) = V (a + j) := by
    rw [I.R.scr _ (by omega), xorV, ifn (by omega)]
  have vb : v.mem (off S (b + j)) = V (b + j) := by
    rw [I.R.scr _ (by omega), xorV, ifn (by omega)]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (off S (b + j)) (V (b + j) ^^^ V (a + j))) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hcv, hdv, I.r8, hea₁, hea₂, I.L.sld8 (d := a + j) (by omega), I.L.sld8 (d := b + j) (by omega),
      I.L.sst8 (d := b + j) (by omega), va, vb, trunc_xor]
  · have R' := I.R.wb I.L.geo (o := b + j) (by omega) (V (b + j) ^^^ V (a + j))
    rw [← hm, ← hm'] at R'
    have R'' : Rep v''.mem F S (xorV V a b (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, xorV]
      by_cases hx : x = b + j
      · subst hx; rw [ifp rfl, ifp (by omega), Nat.add_sub_cancel_left]
      · rw [ifn hx]
        by_cases h' : b ≤ x ∧ x < b + j
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

/-! ## Filling bytes with zeros -/

structure FillI (u₀ : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (o j : Nat) (v : State) : Prop where
  L : Lay v F S
  keep : Keep [.r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  R : Rep v.mem F S (clrV V o j) W

/-- `n` bytes from `scratch + o` (`rcx`) cleared, a byte at a time. -/
theorem fill_ok {u₀ : State} {F S : Addr} (L : Lay u₀ F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u₀.mem F S V W) {o n : Nat} {cnt : Src} (hs : StepOk cnt n u₀ [.r8]) (hn : 0 < n) (ho : o + n ≤ oRsa)
    (hcx : u₀.gpr .rcx = off S o) (hax : u₀.gpr .rax = 0) (h8 : u₀.gpr .r8 = BitVec.ofNat 64 0) :
    WP isa (byteLoop [.store8 (ix .rcx .r8) .rax] cnt) u₀ fun u' =>
      Lay u' F S ∧ Keep [.r8] u₀ u' ∧ Rep u'.mem F S (clrV V o n) W := by
  refine WP.mono (byteLoop_ok hn hs (FillI u₀ F S V W o) ?_ (u := u₀)
    ⟨L, Keep.refl _ _, h8, (congrArg (fun V' => Rep u₀.mem F S V' W) (funext fun x => by
      simp only [clrV]; rw [ifn (by omega)])).mpr R⟩) fun u' I => ⟨I.L, I.keep, I.R⟩
  intro j hj v I
  have hcv : v.gpr .rcx = off S o := (I.keep.gpr (by decide)).trans hcx
  have hav : v.gpr .rax = 0 := (I.keep.gpr (by decide)).trans hax
  have hea : off S o + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (o + j) := by
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, off_plus]
  refine WP.mono (WP.keep [] (Q := fun v' => v'.gpr .r8 = BitVec.ofNat 64 j ∧
      v'.mem = v.mem.writeW (off S (o + j)) (0 : Byte)) ?_ rfl)
    fun v' ⟨⟨h8', hm⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun v'' k' hm' h8'' => ?_⟩
  · xrun [ea_ix, hcv, hav, I.r8, hea, I.L.sst8 (d := o + j) (by omega)]
    rfl
  · have R' := I.R.wb I.L.geo (o := o + j) (by omega) (0 : Byte)
    rw [← hm, ← hm'] at R'
    have R'' : Rep v''.mem F S (clrV V o (j + 1)) W := by
      refine (congrArg (fun V' => Rep v''.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [upd, clrV]
      by_cases hx : x = o + j
      · subst hx; rw [ifp rfl, ifp (by omega)]
      · rw [ifn hx]
        by_cases h' : o ≤ x ∧ x < o + j
        · rw [ifp h', ifp (by omega)]
        · rw [ifn h', ifn (by omega)]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

end VG.Proof.RsaOaep.X86_64
