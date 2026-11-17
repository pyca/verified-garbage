module

public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.DPart
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Crt
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Lcm
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Front
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Halve
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.RsaKeyGen.KeyOp
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `RsaKeyGen.X86_64.Key.Tail`, which only this module used -/

section

/-! ### `RsaKeyGen.X86_64.Key.Main`, which only this module used -/

section

/-! ## Out -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: the outputs

The arrays, masked by `kOk`, to their outputs (`stores_ok`, for any list of
stores to outputs apart from each other), and `kOk`'s low bit returned with
the saved registers restored (`keyExit_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- `storeA` under `kOk`, which keeps the working space and the header. -/
theorem storeK_ws {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j sPtr sLen len : Nat} {out : Addr}
    {c : Bool} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (hp : word s.mem B (8 * sPtr) = out) (hl : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hm : word s.mem B (8 * kOk) = mask c) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hout : ∀ i < len, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (out + BitVec.ofNat 64 i)) :
    WP isa (seqs (storeA j sPtr sLen kOk)) s fun t =>
      (List.range len).map (fun i => t.mem (out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w j) ((len + 7) / 8) else 0) len ∧
      (∀ x, (∀ i < len, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Ws t B Z w ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧
      Keep [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14] s t :=
  WP.mono (storeA_ok h hj hP hL (by decide) hp hl hm hl1 hlw hout hsep) fun t ⟨hb, hx, hwr, hrd, k⟩ =>
    have hf := frm_scr hsep hx
    ⟨hb, hx, h.congr hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega_arith)) k (by decide), hf, k⟩

/-- A store: the array, the header slots of its output's pointer and length,
the output and its length. -/
structure St where
  j : Nat
  p : Nat
  l : Nat
  out : Addr
  len : Nat

/-- The stores of `L`, in order. -/
def storesK : List St → List (Prog isa)
  | [] => []
  | e :: L => storeA e.j e.p e.l kOk ++ storesK L

/-- A store's hypotheses. -/
structure St.Ok (e : St) (s : State) (B : Addr) (Z w : Nat) : Prop where
  j : e.j < 16
  p : e.p < 32
  l : e.l < 32
  hp : word s.mem B (8 * e.p) = e.out
  hl : word s.mem B (8 * e.l) = BitVec.ofNat 64 e.len
  l1 : 1 ≤ e.len
  lw : e.len ≤ 8 * w
  wr : ∀ i < e.len, InRegions s.wr (e.out + BitVec.ofNat 64 i) 1
  sep : ∀ i < e.len, Z ≤ ofs B (e.out + BitVec.ofNat 64 i)

theorem frm_word {m m' : Mem} {B : Addr} {Z : Nat} (hf : Frm B [(Z, 2 ^ 64)] m m') (hZ : 8 * 32 ≤ Z) {i : Nat}
    (hi : i < 32) : word m' B (8 * i) = word m B (8 * i) :=
  hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith)) (by omega_arith)

/-- The registers the stores change. -/
abbrev stRegs : List Reg := [.r12, .r9, .rbx, .rsi, .rcx, .r15, .rax, .rdx, .rbp, .r14]

/-- The stores of `L`, each output apart from the others. -/
theorem stores_ok {B : Addr} {Z w : Nat} {c : Bool} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w →
    word s.mem B (8 * kOk) = mask c → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, (List.range e.len).map (fun i => t.mem (e.out + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot w e.j) ((e.len + 7) / 8) else 0) e.len) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep stRegs s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (storesK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, hm, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨hj, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    rw [storesK, List.append_assoc]
    refine wp_seqs_append (by simp [storeA]) (by cases L <;> simp [storesK, storeA, hr])
      (WP.mono (storeK_ws h hj hp hl hpv hlv hm hl1 hlw hwr hsep) fun s₁ ⟨b₁, x₁, h₁, f₁, k₁⟩ => ?_)
    obtain hpw' := List.pairwise_cons.mp hpw
    refine stores_ok L rest s₁ hr h₁ (by rw [frm_word f₁ h256 (by decide)]; exact hm) (fun e' he' => ?_) hpw'.2
      (fun t ht ft bt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
    · obtain ⟨hj', hp', hl', hpv', hlv', hl1', hlw', hwr', hsep'⟩ := ho e' (List.mem_cons_of_mem _ he')
      exact ⟨hj', hp', hl', by rw [frm_word f₁ h256 hp']; exact hpv', by rw [frm_word f₁ h256 hl']; exact hlv',
        hl1', hlw', fun i hi => by rw [k₁.2.2]; exact hwr' i hi, hsep'⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [← b₁]
        exact List.map_congr_left fun i hi => xt _ fun e'' he''' i' hi' heq =>
          hpw'.1 e'' he''' i (List.mem_range.mp hi) i' hi' heq
      · rw [bt e' he'']
        obtain hj' := (ho e' he').j
        have := (ho e' he').lw
        have := h.sl hj'
        have := h.scr.nowrap
        rw [f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith)) (by omega_arith)]
    · intro x hx
      rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
termination_by structural L => L

/-- `kOk`'s low bit returned and the saved registers restored. -/
theorem keyExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * kOk) = mask c) :
    WP isa (.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, h.rdi, hdrOff, hl kOk (by decide), hm, mask_and1,
      hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
      hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_arith) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- Zeros to each output of `L`. -/
def zerosK (L : List St) : List (Prog isa) := L.map fun e => zeroOut e.p e.l

/-- Zeros to the outputs of `L`, each apart from the others. -/
theorem zeros_ok {B : Addr} {Z w : Nat} {Q : State → Prop} :
    ∀ (L : List St) (rest : List (Prog isa)) (s : State), rest ≠ [] → Ws s B Z w → (∀ e ∈ L, e.Ok s B Z w) →
    L.Pairwise (fun a b => Apart a.out a.len b.out b.len) →
    (∀ t, Ws t B Z w → Frm B [(Z, 2 ^ 64)] s.mem t.mem →
      (∀ e ∈ L, ∀ i < e.len, t.mem (e.out + BitVec.ofNat 64 i) = 0) →
      (∀ x, (∀ e ∈ L, ∀ i < e.len, x ≠ e.out + BitVec.ofNat 64 i) → t.mem x = s.mem x) →
      Keep [.rsi, .rcx, .rax] s t → WP isa (seqs rest) t Q) →
    WP isa (seqs (zerosK L ++ rest)) s Q
  | [], rest, s, _, h, _, _, k => k s h (Frm.refl _ _ _) (by simp) (fun _ _ => rfl) (Keep.refl _ _)
  | e :: L, rest, s, hr, h, ho, hpw, k => by
    have h256 := h.h256
    obtain ⟨_, hp, hl, hpv, hlv, hl1, hlw, hwr, hsep⟩ := ho e List.mem_cons_self
    obtain hpw' := List.pairwise_cons.mp hpw
    obtain hz := zeroOut_ok h.scr h.rdi h256 hp hl hpv hlv hl1 (by have := h.w2; omega_arith) ⟨hwr, hsep⟩
    obtain step : ∀ s₁, ((∀ i < e.len, s₁.mem (e.out + BitVec.ofNat 64 i) = 0) ∧
        (∀ x, (∀ j < e.len, x ≠ e.out + BitVec.ofNat 64 j) → s₁.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s s₁) →
        WP isa (seqs (zerosK L ++ rest)) s₁ Q := by
      intro s₁ ⟨z₁, x₁, k₁⟩
      obtain f₁ := frm_scr hsep x₁
      obtain h₁ : Ws s₁ B Z w := h.congr f₁ (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Or.inl (by omega_arith)) k₁ (by decide)
      refine zeros_ok L rest s₁ hr h₁ (fun e' he' => ?_) hpw'.2
        (fun t ht ft zt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by decide)))
      · obtain ⟨hj', hp', hl', hpv', hlv', hl1', hlw', hwr', hsep'⟩ := ho e' (List.mem_cons_of_mem _ he')
        exact ⟨hj', hp', hl', by rw [frm_word f₁ h256 hp']; exact hpv', by rw [frm_word f₁ h256 hl']; exact hlv',
          hl1', hlw', fun i hi => by rw [k₁.2.2]; exact hwr' i hi, hsep'⟩
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he₂
        · intro i hi
          rw [xt _ fun e₃ he₃ i' hi' heq => hpw'.1 e₃ he₃ i hi i' hi' heq]
          exact z₁ i hi
        · exact zt e' he₂
      · intro x hx
        rw [xt x fun e' he' => hx e' (List.mem_cons_of_mem _ he'), x₁ x (hx e List.mem_cons_self)]
    rw [zerosK, List.map_cons, List.cons_append]
    obtain hne : zerosK L ++ rest ≠ [] := by simp [hr]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [show List.map (fun e => zeroOut e.p e.l) L ++ rest = zerosK L ++ rest from rfl, hcs]
    exact WP.seq (WP.mono hz fun s₁ h₁ => by rw [← hcs]; exact step s₁ h₁)

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Main -/
section

/-!
# An RSA key from its primes on x86-64: from the loads to `smallMask`

`front_k`: after the head, the loads, the order, `p − 1` and `q − 1`,
`L = lcm(p − 1, q − 1)`, `d` and ZF (`Front`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)

/-- The inputs as numbers: `p`, `q`, `e`, ordered, and `L`. -/
abbrev KIn.P₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.pb
abbrev KIn.Q₀ (I : KIn) : Nat := Spec.Rsa.os2ip I.qb
abbrev KIn.E (I : KIn) : Nat := Spec.Rsa.os2ip I.eb
abbrev KIn.P (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.Q₀ else I.P₀
abbrev KIn.Q (I : KIn) : Nat := if I.P₀ < I.Q₀ then I.P₀ else I.Q₀
abbrev KIn.L (I : KIn) : Nat := Nat.lcm (I.P - 1) (I.Q - 1)

/-- The lengths. -/
structure KLens (I : KIn) : Prop where
  pl1 : 32 ≤ I.pl
  pl2 : I.pl ≤ 512
  pl8 : I.pl % 8 = 0
  pbl : I.pb.length = I.pl
  qbl : I.qb.length = I.pl
  ebl : I.eb.length = I.el
  el1 : 1 ≤ I.el
  el8 : I.el ≤ 8

/-- What holds after `smallMask`. -/
structure Front (I : KIn) (m₀ : Mem) (t : State) : Prop where
  ks : KS I m₀ t
  vP : av I t.mem aPa = I.P
  vQ : av I t.mem aQa = I.Q
  vPm : av I t.mem aPm = I.P - 1
  vQm : av I t.mem aQm = I.Q - 1
  ev : word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E
  d : DRes I I.E I.L t.mem
  zf : ∃ ok : Bool, word t.mem I.B (8 * kOk) = mask ok ∧ ((∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true) ∧
    t.zf = some (!(decide (av I t.mem aDd ≤ 2 ^ (8 * I.pl)) && ok))

theorem KLens.W {I : KIn} (L : KLens I) : I.W = 2 * (I.pl / 8) := by
  have := L.pl8; simp only [KIn.W]; omega_arith

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- From the loads to `smallMask`. -/
theorem front_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask))))))) s
      fun t => Front I m₀ t ∧ InScr I.B I.Z s.mem t.mem := by
  have hZ := h.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_arith
  obtain hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  obtain hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  obtain hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_arith))
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA]) (WP.mono (loads_k h L.pbl L.qbl L.ebl
    (by have := L.pl1; omega_arith) (by rw [hW]; have := L.pl8; omega_arith) L.el1 L.el8) fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA]) (by simp [decTo]) (WP.mono (order_k h₁) fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, _⟩ => ?_)
  refine wp_seqs_append (by simp [decTo]) (by simp [lcmPart, phi]) (WP.mono (decTo_k h₃ (o := aQm) (j := aQa)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, vQm₄, _⟩ => ?_)
  obtain hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  obtain hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  obtain vP₄ : av I s₄.mem aPa = I.P := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  obtain vQ₄ : av I s₄.mem aQa = I.Q := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  rw [vP₂] at vPm₃
  rw [f₃.av hok3 (by decide) (by decide) hZ, vQ₂] at vQm₄
  obtain vPm₄ : av I s₄.mem aPm = I.P - 1 := by rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃]
  obtain hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.P, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega_arith
  obtain hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.Q, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega_arith
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi]) (by simp) (WP.mono (lcm_k h₄ hW vPm₄ vQm₄ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hPw)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQw))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  obtain hokL : [Rc.arr aL, Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR,
    Rc.hdr sMo, Rc.hdr kOk, Rc.priv].all Rc.ok = true := by decide
  obtain hokE : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  obtain ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), f₄.word hok4 (by decide) (by decide),
      f₃.word hok3 (by decide) (by decide), f₂.word (by decide) (by decide) (by decide), ev₁]
  obtain hLW : I.L < 2 ^ (64 * I.W) := by
    obtain h1 : I.L ≤ (I.P - 1) * (I.Q - 1) ∨ I.L = 0 := by
      rcases Nat.eq_zero_or_pos ((I.P - 1) * (I.Q - 1)) with h0 | h0
      · right; simp only [KIn.L]
        rcases Nat.mul_eq_zero.mp h0 with h' | h' <;> simp [h']
      · left; exact Nat.le_of_dvd h0 (Nat.lcm_dvd_mul _ _)
    obtain h2 : (I.P - 1) * (I.Q - 1) < 2 ^ (64 * I.W) := by
      rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_arith, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega_arith) (by omega_arith) (Nat.two_pow_pos _)
    rcases h1 with h1 | h1
    · omega_arith
    · rw [h1]; exact Nat.two_pow_pos _
  -- `d`.
  refine wp_seqs_append (by simp) (by simp [smallMask, constA]) ?_
  simp only [seqs]
  refine WP.mono (dPart_k h₅ hE ev₅ vL₅ hLW) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- ZF.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, zf₇⟩ => ?_
  obtain hokD : csD.all Rc.ok = true := by decide
  obtain hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  obtain pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ [Rc.arr aL, Rc.arr aU, Rc.arr aV,
      Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR, Rc.hdr sMo, Rc.hdr kOk, Rc.priv] →
      av I t.mem j = av I s₄.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  obtain okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  obtain hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  obtain hi : InScr I.B I.Z s.mem t.mem := fun x hx => (ht.inScr x hx).trans (h.inScr x hx).symm
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [zf₇, ← hD, show 64 * (I.pl / 8) = 8 * I.pl by omega_arith]⟩⟩, hi⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), vP₄]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), vQ₄]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), vPm₄]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), vQm₄]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end

end

/-! ### `RsaKeyGen.X86_64.Key.NFin`, which only this module used -/

section

/-!
# An RSA key from its primes on x86-64: `n` and the final mask

`n = p q` (`nPart_k`), and `kOk &= ` the masks of `n`'s top bit, `p` and
`q` odd, and `e` valid (`finalMask_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `nPart`: `[aQt] := [aPa] [aQa]`, `w` words each, for `W = 2 w`. -/
theorem nPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPa = a) (hb : av I s.mem aQa = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs nPart) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr aQt] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aQt) (I.W + 2) = a * b := by
  have hn := h.ws.scr.nowrap
  obtain sP := h.ws.sl (j := aPa) (by decide)
  obtain sQ := h.ws.sl (j := aQa) (by decide)
  obtain sL := h.ws.sl (j := aQt) (by decide)
  obtain p1 := slot_far (w := I.W) (i := aPa) (j := aQt) (by decide)
  obtain p2 := slot_far (w := I.W) (i := aQa) (j := aQt) (by decide)
  have hw2 := h.ws.w2
  have hw1 := h.ws.w1
  simp only [nPart, seqs]
  refine WP.seq (WP.mono (zeroA_k h (j := aQt) (by decide)) fun s₁ ⟨h₁, f₁, z₁, _⟩ => ?_)
  obtain hok : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain va : wv s₁.mem I.B (slot I.W aPa) w = a := by
    rw [f₁.wv hok (j := aPa) (by decide) (by decide) (Nat.le_refl _) (by omega_using [hW]) h.hZ, ← ha]
    dsimp only [av] at ha
    exact wv_low_of_lt (by omega_using [hW]) (by rw [ha]; exact ha')
  obtain vb : wv s₁.mem I.B (slot I.W aQa) w = b := by
    rw [f₁.wv hok (j := aQa) (by decide) (by decide) (Nat.le_refl _) (by omega_using [hW]) h.hZ, ← hb]
    dsimp only [av] at hb
    exact wv_low_of_lt (by omega_using [hW]) (by rw [hb]; exact hb')
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h₁.ws.ws_ok fun s₂ ⟨h12, h9, m₂, k₂⟩ => ?_))
  obtain hdi₂ : s₂.gpr .rdi = I.B := (k₂.gpr (by decide)).trans h₁.ws.rdi
  refine WP.block_append_iff.mpr (WP.mono (base_ok aPa (r := .r11) (by decide) hdi₂ h9) fun s₃ ⟨h11, m₃, k₃⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQa (r := .rax) (by decide) ((k₃.gpr (by decide)).trans hdi₂)
    ((k₃.gpr (by decide)).trans h9)) fun s₄ ⟨hax, m₄, k₄⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (base_ok aQt (r := .r8) (by decide)
    (((k₃.trans k₄).gpr (by decide)).trans hdi₂) (((k₃.trans k₄).gpr (by decide)).trans h9))
    fun s₅ ⟨h8, m₅, k₅⟩ => ?_)
  obtain h12₅ : s₅.gpr .r12 = BitVec.ofNat 64 I.W := (((k₃.trans k₄).trans k₅).gpr (by decide)).trans h12
  obtain hax₅ : s₅.gpr .rax = off I.B (slot I.W aQa) := (k₅.gpr (by decide)).trans hax
  refine WP.mono (WP.keep [.r9, .r10, .r12] (Q := fun t => t.gpr .r9 = off I.B (slot I.W aQa) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s₅.mem) (by
    xrun [h12₅, hax₅, ofNat_shr1 (show I.W < 2 ^ 64 by omega_using [hw2])]
    refine ⟨by rw [hW]; congr 1; omega_using [], ?_⟩
    rw [ofNat_sub' (by omega_using []) (by omega_using [hw2])]; congr 1; omega_using [hW]) rfl) fun s₆ ⟨⟨h9₆, h10₆, h12₆, m₆⟩, k₆⟩ => ?_
  obtain k26 := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  obtain hm₆ : s₆.mem = s₁.mem := by rw [m₆, m₅, m₄, m₃, m₂]
  obtain hz₆ : wv s₆.mem I.B (slot I.W aQt) (w + w + 2) = 0 := by rw [hm₆, ← z₁]; congr 1; omega_using [hW]
  refine WP.mono (mulRows_ok (h₁.ws.scr.congr k26.2.2) ((k₄.trans k₅ |>.trans k₆).gpr (by decide) |>.trans h11)
    h9₆ h10₆ h12₆ ((k₆.gpr (by decide)).trans h8) (by omega_using [hW, hw1]) (by omega_using [hW, hw1]) (by omega_using [hW, hw2]) (by omega_using [hW, sL]) (by omega_using [hW, sP])
    (by omega_using [hW, sQ]) (by omega_using [hW, p1]) (by omega_using [hW, p2]) (by rw [hz₆]; exact Nat.two_pow_pos _)) fun t ⟨hv, o, k₇⟩ => ?_
  rw [hz₆, hm₆, va, vb, Nat.zero_add] at hv
  rw [hm₆] at o
  obtain f := KF.arr1 (I := I) (j := aQt) o (Nat.le_refl _) (by omega_using [hW])
  refine ⟨h₁.step f (all_mut_arr (by decide)) (k26.trans k₇) (by decide), (f₁.trans f).mono (by simp), ?_⟩
  rw [show I.W + 2 = w + w + 2 by omega_using [hW]]; exact hv


/-! ## The final mask -/

/-- The top bit of a `W`-word number: of its word `W − 1`. -/
theorem top_bit {m : Mem} {B : Addr} {d W : Nat} (hW : 1 ≤ W) :
    (word m B (d + 8 * (W - 1))).toNat / 2 ^ 63 = if 2 ^ (64 * W - 1) ≤ wv m B d W then 1 else 0 := by
  obtain e : wv m B d W = wv m B d (W - 1) + 2 ^ (64 * (W - 1)) * (word m B (d + 8 * (W - 1))).toNat := by
    rw [show W = W - 1 + 1 from by omega_using [hW], wv]; simp
  obtain ha := wv_lt m B d (W - 1)
  obtain ht := (word m B (d + 8 * (W - 1))).isLt
  generalize wv m B d (W - 1) = a at e ha
  generalize (word m B (d + 8 * (W - 1))).toNat = t at e ht
  obtain hp : 2 ^ (64 * W - 1) = 2 ^ (64 * (W - 1)) * 2 ^ 63 := by rw [← Nat.pow_add]; congr 1; omega_using [hW]
  generalize 2 ^ (64 * (W - 1)) = R at e ha hp
  rw [e, hp]
  by_cases h63 : 2 ^ 63 ≤ t
  · have : R * 2 ^ 63 ≤ R * t := Nat.mul_le_mul_left _ h63
    rw [ite_eq_left (show R * 2 ^ 63 ≤ a + R * t by omega_using [this])]; omega_using [ht, h63]
  · have : R * t + R ≤ R * 2 ^ 63 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [h63])
    rw [ite_eq_right (show ¬ R * 2 ^ 63 ≤ a + R * t by omega_using [ha, this])]; omega_using [h63]


theorem shr63_mask (x : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (x.toNat / 2 ^ 63 = 1)) := by
  obtain h : x >>> 63 = BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := x.isLt; omega_using []
  rw [h]
  have := x.isLt
  rcases (show x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1 by omega_using []) with e | e <;> rw [e] <;> decide

/-- `[rbx + 8 r12 − 8]`: word `W − 1` of the array at `rbx`. -/
theorem addr_last {b : Addr} {B : Addr} {e W : Nat} (hb : b = off B e) (hW : 1 ≤ W) :
    b + BitVec.ofNat 64 W * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = off B (e + 8 * (W - 1)) := by
  subst hb
  obtain h8 : BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  rw [ofNat_mul8, h8, off, off, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  refine congrArg (B + ·) ?_
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega_using [hW]


/-- The mask `finalMask` leaves in `kOk`. -/
abbrev finalOk (W n P Q e : Nat) (ok : Bool) : Bool :=
  decide (2 ^ (64 * W - 1) ≤ n) && ok && decide (P % 2 = 1) && decide (Q % 2 = 1) && Spec.Rsa.exponentValid e

/-- `finalMask`, for `[aQt] = n`, `[aPa] = P`, `[aQa] = Q` and `kOk` the
mask of `ok`. -/
theorem finalMask_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {n P Q e : Nat} {ok : Bool}
    (hn : av I s.mem aQt = n) (hP : av I s.mem aPa = P) (hQ : av I s.mem aQa = Q) (he64 : e < 2 ^ 64)
    (hev : word s.mem I.B (8 * kEv) = BitVec.ofNat 64 e) (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa (.block finalMask) s fun t => KS I m₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask (finalOk I.W n P Q e ok) := by
  have hnw := h.ws.scr.nowrap
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_using [this]
  obtain sN := h.ws.sl (j := aQt) (by decide)
  obtain hld := fun (i : Nat) (hi : i < 32) => h.ws.scr.ld (d := 8 * i) (by have := h.ws.h256; omega_using [hi, this])
  unfold finalMask
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws.ws_ok fun u₁ ⟨h12, h9, mu₁, ku₁⟩ => WP.block_append_iff.mpr ?_)
  obtain hdi₁ : u₁.gpr .rdi = I.B := (ku₁.gpr (by decide)).trans h.ws.rdi
  refine WP.mono (base_ok aQt (r := .rbx) (by decide) hdi₁ h9) fun u₂ ⟨hbx, mu₂, ku₂⟩ => WP.block_append_iff.mpr ?_
  obtain hs₂ := h.ws.scr.congr (ku₁.trans ku₂).2.2
  obtain h12₂ : u₂.gpr .r12 = BitVec.ofNat 64 I.W := (ku₂.gpr (by decide)).trans h12
  obtain hmu₂ : u₂.mem = s.mem := by rw [mu₂, mu₁]
  obtain htop : (word s.mem I.B (slot I.W aQt + 8 * (I.W - 1))).toNat / 2 ^ 63 = 1 ↔ 2 ^ (64 * I.W - 1) ≤ n := by
    rw [top_bit hw1, show wv s.mem I.B (slot I.W aQt) I.W = n from hn]; split <;> simp_all
  -- `rcx := ` the masks of the top bit and `ok`.
  refine WP.mono (WP.keep [.rax, .rdx, .rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) ∧
    t.mem = s.mem) (by
      obtain hok₂ : word u₂.mem I.B (8 * kOk) = mask ok := by rw [hmu₂, hok]
      xrun [State.ea, ix, hdr, hdrOff, h12₂, addr_last hbx hw1, hs₂.ld (d := slot I.W aQt + 8 * (I.W - 1)) (by omega_using [sN]),
        ((ku₁.trans ku₂).gpr (by decide)).trans h.ws.rdi, hs₂.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]),
        shr63_mask, hok₂, mask_and', hmu₂]
      have hok' : s.mem.readW (off I.B (8 * kOk)) 64 = mask ok := hok
      obtain ht' : decide ((s.mem.readW (off I.B (slot I.W aQt + 8 * (I.W - 1))) 64).toNat / 2 ^ 63 = 1) =
          decide (2 ^ (64 * I.W - 1) ≤ n) := decide_eq_decide.mpr htop
      rw [hok', mask_and', ht']) rfl) fun u₃ ⟨⟨hcx₃, mu₃⟩, ku₃⟩ => WP.block_append_iff.mpr ?_
  obtain k13 := (ku₁.trans ku₂).trans ku₃
  obtain h₃ := h.step (cs := []) (by rw [mu₃]; exact KF.refl _ _ _) rfl k13 (by decide)
  -- `p` odd.
  refine WP.mono (oddMask_k h₃ (j := aPa) (by decide)) fun u₄ ⟨mu₄, hax₄, _, _, ku₄⟩ => WP.block_append_iff.mpr ?_
  rw [mu₃, hP] at hax₄
  obtain hcx₄ : u₄.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok) := by rw [ku₄.gpr (by decide), hcx₃]
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok &&
    decide (P % 2 = 1)) ∧ t.mem = u₄.mem) (by xrun [hax₄, hcx₄, mask_and']) rfl)
    fun u₅ ⟨⟨hcx₅, mu₅⟩, ku₅⟩ => WP.block_append_iff.mpr ?_
  obtain h₅ := h₃.step (cs := []) (by rw [mu₅, mu₄]; exact KF.refl _ _ _) rfl (ku₄.trans ku₅) (by decide)
  -- `q` odd.
  refine WP.mono (oddMask_k h₅ (j := aQa) (by decide)) fun u₆ ⟨mu₆, hax₆, _, _, ku₆⟩ => ?_
  rw [mu₅, mu₄, mu₃, hQ] at hax₆
  obtain hcx₆ : u₆.gpr .rcx = mask (decide (2 ^ (64 * I.W - 1) ≤ n) && ok && decide (P % 2 = 1)) := by
    rw [ku₆.gpr (by decide), hcx₅]
  obtain hm₆ : u₆.mem = s.mem := by rw [mu₆, mu₅, mu₄, mu₃]
  obtain hs₆ := h₅.ws.scr.congr ku₆.2.2
  obtain hdi₆ : u₆.gpr .rdi = I.B := ((ku₄.trans ku₅).trans ku₆).gpr (by decide) |>.trans h₃.ws.rdi
  obtain hev₆ : u₆.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := by rw [hm₆]; exact hev
  -- `e` valid, and the store.
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk))
    (mask (finalOk I.W n P Q e ok))) (by
      xrun [State.ea, hdr, hdi₆, hdrOff, hs₆.ld (d := 8 * kEv) (by have := h.ws.h256; unfold kEv sFn; omega_using [this]),
        hs₆.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this]), hev₆, hax₆, hcx₆, mask_and', mask_low,
        sxM1, maskNot, hm₆]
      have hev' : s.mem.readW (off I.B (8 * kEv)) 64 = BitVec.ofNat 64 e := hev
      obtain hT : ((BitVec.ofNat 64 e) >>> 33).toNat = e / 2 ^ 33 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64]
      obtain hsub : ∀ c : Bool, 0#64 - BitVec.setWidth 64 (BitVec.ofBool c) = mask c := fun _ => rfl
      rw [hev', BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hT, hsub, hsub, maskNot, mask_and', mask_and',
        show BitVec.toNat (3 : BitVec 64) = 3 from rfl, show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
      obtain e1 : (decide (e % 2 = 1) && !decide (e < 3) && decide (e / 2 ^ 33 < 1)) = Spec.Rsa.exponentValid e := by
        unfold Spec.Rsa.exponentValid
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        omega_using []
      refine congrArg (fun v => s.mem.writeW (off I.B (8 * kOk)) (mask v)) ?_
      simp only [finalOk]
      rw [← e1]
      simp only [Bool.and_assoc]) rfl) fun t ⟨mt, kt⟩ => ?_
  obtain ⟨ht, ft, okt⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) mt
    ((((k13.trans ku₄).trans ku₅).trans ku₆).trans kt) (by decide)
  exact ⟨ht, ft, okt⟩

end VG.Proof.RsaKeyGen.X86_64.Key

end

end


/-!
# An RSA key from its primes on x86-64: the key

`keyPart`, once `d` is not too small or does not exist: `qInv`, `dP`, `dQ`,
`n`, the final mask, the stores and the exit (`keyPart_k`); and the zeros
and the status 2 otherwise (`zerosPart_k`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- The outputs, in the order of the stores. -/
def outsL (I : KIn) : List (Addr × Nat) :=
  [(I.pN, 2 * I.pl), (I.pD, 2 * I.pl), (I.pP, I.pl), (I.pQ, I.pl), (I.pDp, I.pl), (I.pDq, I.pl), (I.pQi, I.pl)]

/-- The stores. -/
def storeL (I : KIn) : List St :=
  [⟨aQt, kNo, kNl, I.pN, 2 * I.pl⟩, ⟨aDd, kDo, kNl, I.pD, 2 * I.pl⟩, ⟨aPa, kPp, kPl, I.pP, I.pl⟩,
    ⟨aQa, kQp, kPl, I.pQ, I.pl⟩, ⟨aX₁, kDp, kPl, I.pDp, I.pl⟩, ⟨aV, kDq, kPl, I.pDq, I.pl⟩,
    ⟨aX₂, kQi, kPl, I.pQi, I.pl⟩]

/-- The outputs: writable, outside the working space, apart. -/
structure KOuts (I : KIn) : Prop where
  wr : ∀ o ∈ outsL I, ∀ i < o.2, InRegions I.Wr (o.1 + BitVec.ofNat 64 i) 1
  sep : ∀ o ∈ outsL I, ∀ i < o.2, I.Z ≤ ofs I.B (o.1 + BitVec.ofNat 64 i)
  apart : (outsL I).Pairwise fun a b => Apart a.1 a.2 b.1 b.2

theorem storeL_outs (I : KIn) : (storeL I).map (fun e => (e.out, e.len)) = outsL I := rfl

theorem storeL_pairwise {I : KIn} (O : KOuts I) :
    (storeL I).Pairwise fun a b => Apart a.out a.len b.out b.len := by
  have := O.apart
  rw [← storeL_outs, List.pairwise_map] at this
  exact this

theorem st_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (O : KOuts I) {j p l : Nat} {out : Addr}
    {len : Nat} (hj : j < 16) (hp : p < 32) (hl : l < 32) (hpv : word t.mem I.B (8 * p) = out)
    (hlv : word t.mem I.B (8 * l) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W)
    (ho : (out, len) ∈ outsL I) : (⟨j, p, l, out, len⟩ : St).Ok t I.B I.Z I.W :=
  ⟨hj, hp, hl, hpv, hlv, hl1, hlw, fun i hi => by rw [h.wr]; exact O.wr _ ho i hi, O.sep _ ho⟩

theorem storeL_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (L : KLens I) (O : KOuts I) :
    ∀ e ∈ storeL I, e.Ok t I.B I.Z I.W := by
  have hW := L.W
  have hpl := L.pl1
  have h8 := L.pl8
  intro e he
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.no h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dd h.args.nl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.pp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dp h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dq h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qi h.args.pl (by omega_using [hpl]) (by omega_using [hW, h8]) (by simp [outsL])

theorem outputs_eq (I : KIn) : outputs = storesK (storeL I) ++
    ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa)) := rfl

theorem zeros_eq (I : KIn) (st : Nat) : zeros st = seqs (zerosK (storeL I) ++
    ([.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)] : List (Prog isa))) := rfl

theorem keyPart_eq (I : KIn) : keyPart = seqs (qinvPart ++ (crtPart ++ (nPart ++ (([.block finalMask] : List (Prog isa)) ++
    (storesK (storeL I) ++ ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa))))))) := by
  rw [keyPart, ← outputs_eq I]; simp only [List.append_assoc]

/-- A number below `2^(64 v)` read from `v ≤ W` words. -/
theorem wv_of_av {I : KIn} {m : Mem} {j v x : Nat} (hv : v ≤ I.W) (h : av I m j = x) (hx : x < 2 ^ (64 * v)) :
    wv m I.B (slot I.W j) v = x := by
  rw [← h]; exact wv_low_of_lt hv (by rw [show wv m I.B (slot I.W j) I.W = av I m j from rfl, h]; exact hx)

/-- What `keyPart` leaves, from `Front` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `keyPart`. -/
theorem keyPart_k [InvLaw] {I : KIn} {m₀ : Mem} {s : State} (h : Front I m₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  obtain hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega_using [this]
  obtain hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.P, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega_arith
  obtain hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.Q, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega_arith
  rw [keyPart_eq I]
  -- `qInv`.
  refine wp_seqs_append (by simp [qinvPart]) (by simp [crtPart, divisorOf]) (WP.mono (qinvPart_k hk h.vP h.vQ hok
    (by have := L.pl1; omega_using [hW, this]) (by rw [show I.W / 2 = I.pl / 8 by omega_using [hW]]; exact hPw)
    (by rw [show I.W / 2 = I.pl / 8 by omega_using [hW]]; exact hQw))
    fun s₁ ⟨h₁, f₁, ok₁, hdv₁, hx₁⟩ => ?_)
  generalize hx : av I s₁.mem aX₂ = x at hdv₁ hx₁
  obtain hokQ : csQ.all Rc.ok = true := by decide
  -- `dP`, `dQ`.
  refine wp_seqs_append (by simp [crtPart, divisorOf]) (by simp [nPart]) (WP.mono (crtPart_k h₁
    (d := av I s.mem aDd) (a := I.P - 1) (b := I.Q - 1) (by rw [f₁.av hokQ (by decide) (by decide) hZ])
    (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vPm]) (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vQm]))
    fun s₂ ⟨h₂, f₂, dP₂, dQ₂⟩ => ?_)
  obtain hokC : csC.all Rc.ok = true := by decide
  -- `n`.
  refine wp_seqs_append (by simp [nPart]) (by simp) (WP.mono (nPart_k h₂ hW
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vP)
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vQ) hPw hQw)
    fun s₃ ⟨h₃, f₃, n₃⟩ => ?_)
  obtain hn : I.P * I.Q < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega_using [hQw]) (Nat.two_pow_pos _)
  obtain hokN : [Rc.arr aQt].all Rc.ok = true := by decide
  obtain vN₃ : av I s₃.mem aQt = I.P * I.Q := av_of_full n₃ hn
  obtain vP₃ : av I s₃.mem aPa = I.P := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vP]
  obtain vQ₃ : av I s₃.mem aQa = I.Q := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vQ]
  obtain ev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide),
      f₁.word hokQ (by decide) (by decide), h.ev]
  obtain ok₃ : word s₃.mem I.B (8 * kOk) = mask (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide), ok₁]
  obtain hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_arith))
  -- The final mask.
  refine wp_seqs_append (by simp) (by simp [storesK, storeL, storeA]) ?_
  simp only [seqs]
  refine WP.mono (finalMask_k h₃ vN₃ vP₃ vQ₃ hE ev₃ ok₃) fun s₄ ⟨h₄, f₄, ok₄⟩ => ?_
  generalize hc : finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) = cv at ok₄
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  obtain v4 : ∀ j, j < 16 → Rc.arr j ∉ [Rc.arr aQt] → Rc.arr j ∉ csC → Rc.arr j ∉ csQ →
      av I s₄.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₄.av hokO hj (by simp) hZ, f₃.av hokN hj h1 hZ, f₂.av hokC hj h2 hZ, f₁.av hokQ hj h3 hZ]
  -- The stores and the exit.
  refine stores_ok (Q := fun t => TailPost I s t ok) (storeL I) _ s₄ (by simp) h₄.ws ok₄ (storeL_ok h₄ L O)
    (storeL_pairwise O) fun t ht ft bt xt kt => ?_
  simp only [seqs]
  refine WP.mono (keyExit_ok ht (c := cv) (by rw [frm_word ft ht.h256 (by decide)]; exact ok₄))
    fun u ⟨hax, hsv, hmu, ku⟩ => ?_
  obtain b := fun e he => (bt e he)
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b
  obtain ⟨bN, bD, bP, bQ, bDp, bDq, bQi⟩ := b
  obtain hlen : (I.pl + 7) / 8 = I.pl / 8 := by have := L.pl8; omega_using [this]
  obtain hlen2 : (2 * I.pl + 7) / 8 = I.W := by have := L.pl8; simp only [KIn.W]; omega_using [this]
  obtain hv : I.pl / 8 ≤ I.W := by omega_using [hlen2]
  obtain hdvw : ∀ a, a ≤ I.P → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hPw, ha]
  obtain hdvwq : ∀ a, a ≤ I.Q → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega_using [this])
    · omega_using [hQw, ha]
  obtain hdv0 : ∀ a, 0 < dv a := fun a => by unfold dv; split <;> omega_arith
  obtain hqm : qMod I.P < 2 ^ (64 * (I.pl / 8)) := by
    unfold qMod; split
    · exact hPw
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ 64 * (I.pl / 8) by
        have := L.pl1; omega_using [this]))
  obtain iv : ∀ {len v : Nat} {o : Addr} {w' : Nat},
      (List.range len).map (fun i => t.mem (o + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if cv then w' else 0) len → w' = v →
      Spec.Rsa.bytesAt u.mem o len = Spec.Rsa.i2osp (if cv = true then v else 0) len := fun hb hw => by
    simp only [Spec.Rsa.bytesAt]; rw [hmu, hb, hw]
  refine ⟨x, hdv₁, hx₁, ?_, fun i hi => ?_, fun y hy hny => ?_, ?_⟩
  · dsimp only
    rw [hc]
    refine ⟨hax, iv bN ?_, iv bD ?_, iv bP ?_, iv bQ ?_, iv bDp ?_, iv bDq ?_, iv bQi ?_⟩
    · rw [hlen2]; show av I s₄.mem aQt = _; rw [f₄.av hokO (by decide) (by decide) hZ, vN₃]
    · rw [hlen2]; exact v4 aDd (by decide) (by decide) (by decide) (by decide)
    · rw [hlen]; exact wv_of_av hv (v4 aPa (by decide) (by decide) (by decide) (by decide) |>.trans h.vP) hPw
    · rw [hlen]; exact wv_of_av hv (v4 aQa (by decide) (by decide) (by decide) (by decide) |>.trans h.vQ) hQw
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dP₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvw _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dQ₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvwq _ (by omega_using []))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ,
        f₂.av hokC (by decide) (by decide) hZ, hx]) (by omega_using [hx₁, hqm])
  · rw [hsv i hi, frm_word ft ht.h256 (by omega_using [hi])]; exact h₄.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy', h₄.inScr y hy, hk.inScr y hy]
  · rw [ku.gpr (by decide), kt.gpr (by decide), h₄.rsp]

/-- The status `st` returned and the saved registers restored. -/
theorem stExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (st : Nat) :
    WP isa (.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧
        (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, h.rdi, hdrOff, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .rax = (BitVec.ofNat 32 2).setWidth 64 ∧
    (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `zeros 2`: zeros to the outputs, and the status 2. -/
theorem zerosPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s) := by
  rw [zeros_eq I]
  refine zeros_ok (storeL I) _ s (by simp) h.ws (storeL_ok h L O) (storeL_pairwise O)
    fun t ht ft zt xt kt => ?_
  simp only [seqs]
  refine WP.mono (stExit_ok ht 2) fun u ⟨hax, hsv, hmu, ku⟩ => ⟨hax, fun o ho => ?_, fun i hi => ?_,
    fun y hy hny => ?_, ?_⟩
  · rw [← storeL_outs] at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hmu]; exact zt e he i (List.mem_range.mp hi)
  · rw [hsv i hi, frm_word ft ht.h256 (by omega_using [hi])]; exact h.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy']
  · rw [ku.gpr (by decide), kt.gpr (by decide), h.rsp]

end VG.Proof.RsaKeyGen.X86_64.Key

end

end


/-! ## Ctx -/

@[expose] public section

section

/-!
# An RSA key from its primes on x86-64: the precondition, as the code uses it

`keyIn s`: the inputs, from the state on entry; `KCtx s`: what the code
uses of `keyPre` (`keyCtx_of`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

/-- The inputs, from the state on entry. -/
def keyIn (s : State) : KIn where
  B := arg s 10
  Z := (arg s 11).toNat * 8
  pl := (s.gpr .r9).toNat
  pN := s.gpr .rdi
  pD := s.gpr .rdx
  pP := s.gpr .r8
  pQ := arg s 0
  pDp := arg s 2
  pDq := arg s 4
  pQi := arg s 6
  pE := arg s 8
  el := (arg s 9).toNat
  sv i := s.gpr (saved.getD i .rax)
  pb := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  qb := bytesAt s.mem (arg s 0) (s.gpr .r9).toNat
  eb := bytesAt s.mem (arg s 8) (arg s 9).toNat
  Wr := s.wr
  sp := s.gpr .rsp

/-- What the code uses of `keyPre`. -/
structure KCtx (s : State) : Prop where
  L : KLens (keyIn s)
  rsi : (s.gpr .rsi).toNat = 2 * (s.gpr .r9).toNat
  hs : Scr s (arg s 10) ((arg s 11).toNat * 8)
  hZ : slot (keyIn s).W 26 ≤ (arg s 11).toNat * 8
  ha : ∀ j < 11, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 11, ∀ m', Outside (arg s 10) 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j
  p : Src s (arg s 10) ((arg s 11).toNat * 8) (s.gpr .r8) (keyIn s).pb
  q : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 0) (keyIn s).qb
  e : Src s (arg s 10) ((arg s 11).toNat * 8) (arg s 8) (keyIn s).eb
  O : KOuts (keyIn s)
  hret : ∀ b < 8, (arg s 11).toNat * 8 ≤ ofs (arg s 10) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ o ∈ outsL (keyIn s), ∀ i < o.2, s.gpr .rsp + BitVec.ofNat 64 b ≠ o.1 + BitVec.ofNat 64 i

theorem kStk_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega_using []]

theorem kStk_add (s : State) (j b : Nat) :
    stackArgAddr s j + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j + b) := by
  rw [kStk_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem kApart_of {o₁ o₂ : Addr} {l₁ l₂ : Nat} (hd : (⟨o₁, l₁⟩ : Region).Disjoint ⟨o₂, l₂⟩) (h₁ : l₁ ≤ 2 ^ 64)
    (h₂ : l₂ ≤ 2 ^ 64) : Apart o₁ l₁ o₂ l₂ := fun i hi j hj he =>
  hd _ (contains_byte o₁ hi h₁) (by rw [he]; exact contains_byte o₂ hj h₂)

theorem keyCtx_of {s : State} (h : keyPre s) : KCtx s := by
  simp only [keyPre] at h
  sig_split h
  rename_i hsp hrd hwr dnd dnp dnq dndp dndq dnqi dne dns dna ddp ddq dddp dddq ddqi dde dds dda dpq
    dpdp dpdq dpqi dpe dps dpa dqdp dqdq dqqi dqe dqs dqa dpdq' dpqi' dpe' dps' dpa' dqqi' dqe' dqs'
    dqa' dqie dqis dqia des dsa dRn dRd dRp dRq dRdp dRdq dRqi dRe dRs dRa wn wd wp wq wdp wdq wqi
    we ws hpl hsi hcx hql hdpl hdql hqil hel1 hel8
  have hsl := h
  obtain ⟨hpl1, hpl2, hpl8⟩ := hpl
  unfold Spec.Rsa.scratchWords at hsl
  obtain hs : Scr s (arg s 10) ((arg s 11).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) ws
  have hn := hs.nowrap
  obtain hargs : (⟨stackArgAddr s 0, 96⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  simp only [hcx, hsi] at dnd ddp ddq dddp dddq ddqi dde dds dda dRd wd
  simp only [hsi] at dnp dnq dndp dndq dnqi dne dns dna dRn wn
  simp only [hql] at dnq ddq dpq dqdp dqdq dqqi dqe dqs dqa dRq wq
  simp only [hdpl] at dndp dddp dpdp dqdp dpdq' dpqi' dpe' dps' dpa' dRdp wdp
  simp only [hdql] at dndq dddq dpdq dqdq dpdq' dqqi' dqe' dqs' dqa' dRdq wdq
  simp only [hqil] at dnqi ddqi dpqi dqqi dpqi' dqqi' dqie dqis dqia dRqi wqi
  obtain hwr' : ∀ (o : Addr) (l : Nat), (⟨o, l⟩ : Region) ∈ s.wr → l ≤ 2 ^ 64 → ∀ i < l,
      InRegions s.wr (o + BitVec.ofNat 64 i) 1 := fun o l hm hl i hi => ⟨_, hm, contains_byte o hi hl⟩
  obtain hpw : (s.gpr .r9).toNat ≤ 2 ^ 64 := by omega_using []
  refine ⟨⟨hpl1, hpl2, hpl8, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, hel1, hel8⟩, hsi, hs,
    by simp only [keyIn, KIn.W, slot, hdrBytes]; omega_using [hsi, hsl, hpl1],
    fun j hj => ⟨_, hargs, by rw [kStk_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 96) (by omega_using [hj, hb]) (by omega_using []))
      rw [← kStk_add s j b] at this; omega_using [hsl, this])),
    src_of_region (by rw [hwr]; simp) (by omega_using []) dps,
    src_of_region (by rw [hwr]; simp [hql]) (by omega_using []) dqs,
    src_of_region (by rw [hrd]; simp) (by omega_using []) des,
    ⟨fun o ho => ?_, fun o ho => ?_, ?_⟩, fun b hb => ?_⟩
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · exact hwr' _ _ (by rw [hwr, hsi]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr, hcx, hsi]; simp) (by omega_using [wn])
    · exact hwr' _ _ (by rw [hwr]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hql]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdpl]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hdql]; simp) (by omega_using [])
    · exact hwr' _ _ (by rw [hwr, hqil]; simp) (by omega_using [])
  · simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> intro i hi
    · exact out_scr dns (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dds (contains_byte _ hi (by omega_using [wn]))
    · exact out_scr dps (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs (contains_byte _ hi (by omega_using []))
    · exact out_scr dps' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqs' (contains_byte _ hi (by omega_using []))
    · exact out_scr dqis (contains_byte _ hi (by omega_using []))
  · simp only [outsL, keyIn, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
    exact ⟨⟨kApart_of dnd (by omega_using [wn]) (by omega_using [wn]), kApart_of dnp (by omega_using [wn]) (by omega_using []),
        kApart_of dnq (by omega_using [wn]) (by omega_using []), kApart_of dndp (by omega_using [wn]) (by omega_using []),
        kApart_of dndq (by omega_using [wn]) (by omega_using []), kApart_of dnqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of ddp (by omega_using [wn]) (by omega_using []), kApart_of ddq (by omega_using [wn]) (by omega_using []),
        kApart_of dddp (by omega_using [wn]) (by omega_using []), kApart_of dddq (by omega_using [wn]) (by omega_using []),
        kApart_of ddqi (by omega_using [wn]) (by omega_using [])⟩,
      ⟨kApart_of dpq (by omega_using []) (by omega_using []), kApart_of dpdp (by omega_using []) (by omega_using []),
        kApart_of dpdq (by omega_using []) (by omega_using []), kApart_of dpqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dqdp (by omega_using []) (by omega_using []), kApart_of dqdq (by omega_using []) (by omega_using []),
        kApart_of dqqi (by omega_using []) (by omega_using [])⟩,
      ⟨kApart_of dpdq' (by omega_using []) (by omega_using []), kApart_of dpqi' (by omega_using []) (by omega_using [])⟩,
      kApart_of dqqi' (by omega_using []) (by omega_using [])⟩
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega_using [hb]) (by omega_using [])
    refine ⟨out_scr dRs hc, fun o ho i hi he => ?_⟩
    simp only [outsL, keyIn, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at hi he
    · exact dRn _ hc (by rw [he]; exact contains_byte _ hi (by omega_using [wn]))
    · exact dRd _ hc (by rw [he]; exact contains_byte _ hi (by omega_using [wn]))
    · exact dRp _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRq _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRdp _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRdq _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))
    · exact dRqi _ hc (by rw [he]; exact contains_byte _ hi (by omega_using []))

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## Res -/
section

/-!
# An RSA key from its primes on x86-64: the results, against `keyOp`

What the zeros (`outsRes_zeros`) and `keyPart` (`outsRes_tail`) leave is
`keyOp`'s status and outputs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)
open VG.Spec.RsaKeyGen (keyFromPrimes)
open VG.Proof.RsaKeyGen (keyOp keyStatus)

/-- The status and the outputs `keyOp` gives. -/
def OutsRes (I : KIn) (m : Mem) (rax : BitVec 64) : Prop :=
  (rax.setWidth 32).toNat = keyStatus (keyOp I.pl I.eb I.pb I.qb) ∧
    match keyOp I.pl I.eb I.pb I.qb with
    | .inl (.ok ys) => (outsL I).map (fun o => bytesAt m o.1 o.2) = ys
    | _ => ∀ o ∈ outsL I, bytesAt m o.1 o.2 = List.replicate o.2 0

theorem keyOp_inr {pl : Nat} {eB pB qB : List Byte}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) = .inr ()) :
    keyOp pl eB pB qB = .inr () := by
  unfold keyOp; rw [h]

theorem keyOp_error {pl : Nat} {eB pB qB : List Byte} {f : Spec.RsaKeyGen.Failure}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.error f)) :
    keyOp pl eB pB qB = .inl (.error f) := by
  unfold keyOp; rw [h]

theorem keyOp_ok {pl : Nat} {eB pB qB : List Byte} {k : Spec.RsaKeyGen.Key}
    (h : keyFromPrimes (16 * pl) (Spec.Rsa.os2ip eB) (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB) =
      .inl (.ok k)) :
    keyOp pl eB pB qB = .inl (.ok [Spec.Rsa.i2osp k.n (2 * pl), Spec.Rsa.i2osp k.d (2 * pl),
      Spec.Rsa.i2osp k.p pl, Spec.Rsa.i2osp k.q pl, Spec.Rsa.i2osp k.dP pl,
      Spec.Rsa.i2osp k.dQ pl, Spec.Rsa.i2osp k.qInv pl]) := by
  unfold keyOp; rw [h]

theorem setWidth32 (n : Nat) (h : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega_using [h]),
    Nat.mod_eq_of_lt h]

/-- The zeros and the status 2, for `d ≤ 2^(8 pl)`. -/
theorem outsRes_zeros {I : KIn} {s t : State} {d : Nat}
    (hd : Spec.Rsa.inverse I.E I.L = some d) (hsm : d ≤ 2 ^ (8 * I.pl)) (Z : ZerosPost I s t) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain hr : keyFromPrimes (16 * I.pl) I.E I.P₀ I.Q₀ = .inr () := by
    unfold keyFromPrimes
    obtain hswap : (if I.P₀ < I.Q₀ then (I.Q₀, I.P₀) else (I.P₀, I.Q₀)) = (I.P, I.Q) := by
      by_cases h : I.P₀ < I.Q₀ <;> simp [KIn.P, KIn.Q, h]
    rw [hswap]
    dsimp only
    rw [show Nat.lcm (I.P - 1) (I.Q - 1) = I.L from rfl, hd, show 16 * I.pl / 2 = 8 * I.pl by omega_using []]
    dsimp only
    rw [ite_eq_left hsm]
  rw [OutsRes, keyOp_inr hr, Z.1]
  exact ⟨by decide, Z.2.1⟩

theorem i2osp_zero (k : Nat) : Spec.Rsa.i2osp 0 k = List.replicate k 0 := by
  simp [Spec.Rsa.i2osp, List.map_const']

/-- The outputs and the status of `keyPart`, for `d > 2^(8 pl)` or no `d`. -/
theorem outsRes_tail {I : KIn} {s t : State} (L : KLens I) {ok : Bool}
    (hok : (∃ d, Spec.Rsa.inverse I.E I.L = some d) ↔ ok = true)
    (hdd : ∀ d, Spec.Rsa.inverse I.E I.L = some d → av I s.mem aDd = d)
    (hb : (decide (av I s.mem aDd ≤ 2 ^ (8 * I.pl)) && ok) = false) (T : TailPost I s t ok) :
    OutsRes I t.mem (t.gpr .rax) := by
  obtain ⟨x, hx, hxl, ⟨hax, hN, hD, hP, hQ, hDp, hDq, hQi⟩, -⟩ := T
  obtain he : I.E < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (lt_of_os2ip_len L.ebl) (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega_using [this]))
  obtain hk := keyFromPrimes_code (x := x) L.pl1 L.pl2 (lt_of_os2ip_len L.pbl) (lt_of_os2ip_len L.qbl) he hx hxl
  obtain hW : 64 * I.W - 1 = 16 * I.pl - 1 := by rw [L.W]; have := L.pl8; omega_using [this]
  simp only [finalOk, hW] at hax hN hD hP hQ hDp hDq hQi
  obtain hstat : ∀ c : Bool, ((BitVec.ofNat 64 c.toNat).setWidth 32).toNat = c.toNat := fun c =>
    setWidth32 _ (by cases c <;> decide)
  rcases hi : Spec.Rsa.inverse I.E I.L with _ | d
  · have hok' : ok = false := by
      cases ok
      · rfl
      · obtain ⟨d, hd⟩ := hok.mpr rfl; rw [hi] at hd; cases hd
    subst hok'
    simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, i2osp_zero, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    rw [OutsRes, keyOp_error hk, hax, hstat]
    refine ⟨rfl, ?_⟩
    simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
  · have hok' : ok = true := hok.mp ⟨d, hi⟩
    subst hok'
    obtain hd := hdd d hi
    rw [hd, Bool.and_true, decide_eq_false_iff_not] at hb
    obtain hd2 : 2 ≤ d := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ 8 * I.pl by have := L.pl1; omega_using [this])
      omega_using [hb, this]
    obtain hqp : I.Q ≤ I.P := by simp only [KIn.P, KIn.Q]; split <;> omega_arith
    obtain ⟨hP3, hQ2, -⟩ := primes_of_inverse hqp hi hd2
    obtain hdvP : dv (I.P - 1) = I.P - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hP3]
    obtain hdvQ : dv (I.Q - 1) = I.Q - 1 := by simp only [dv]; rw [ite_eq_right_iff]; omega_using [hQ2]
    simp only [Bool.and_true, KIn.L] at hax hN hD hP hQ hDp hDq hQi hi hk
    rw [hi] at hk
    simp only [ite_eq_right_iff.mpr (fun h => absurd h hb)] at hk
    simp only [hd, hdvP, hdvQ] at hD hDp hDq
    generalize hc : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qMod I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c
      at hax hN hD hP hQ hDp hDq hQi
    have hc' : (decide (2 ^ (16 * I.pl - 1) ≤ I.P * I.Q) && decide (Nat.gcd I.Q (qModP I.P) = 1) &&
      decide (I.P % 2 = 1) && decide (I.Q % 2 = 1) && Spec.Rsa.exponentValid I.E) = c := hc
    rw [hc'] at hk
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte] at hk
      rw [OutsRes, keyOp_error hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      simp only [Bool.false_eq_true, ↓reduceIte, i2osp_zero] at hN hD hP hQ hDp hDq hQi
      exact ⟨hN, hD, hP, hQ, hDp, hDq, hQi⟩
    · simp only [↓reduceIte] at hk hN hD hP hQ hDp hDq hQi
      rw [OutsRes, keyOp_ok hk, hax, hstat]
      refine ⟨rfl, ?_⟩
      simp only [outsL, List.map_cons, List.map_nil, hN, hD, hP, hQ, hDp, hDq, hQi]

end VG.Proof.RsaKeyGen.X86_64.Key

end
