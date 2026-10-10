import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Entry
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail

/-! ## Out -/
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
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h.h256; omega)) k (by decide), hf, k⟩

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
  hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)

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
    have hpw' := List.pairwise_cons.mp hpw
    refine stores_ok L rest s₁ hr h₁ (by rw [frm_word f₁ h256 (by decide)]; exact hm) (fun e' he' => ?_) hpw'.2
      (fun t ht ft bt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by simp)))
    · obtain ⟨hj', hp', hl', hpv', hlv', hl1', hlw', hwr', hsep'⟩ := ho e' (List.mem_cons_of_mem _ he')
      exact ⟨hj', hp', hl', by rw [frm_word f₁ h256 hp']; exact hpv', by rw [frm_word f₁ h256 hl']; exact hlv',
        hl1', hlw', fun i hi => by rw [k₁.2.2]; exact hwr' i hi, hsep'⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [← b₁]
        exact List.map_congr_left fun i hi => xt _ fun e'' he''' i' hi' heq =>
          hpw'.1 e'' he''' i (List.mem_range.mp hi) i' hi' heq
      · rw [bt e' he'']
        have hj' := (ho e' he').j
        have := (ho e' he').lw
        have := h.sl hj'
        have := h.scr.nowrap
        rw [f₁.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega)]
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
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
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
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
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
    have hpw' := List.pairwise_cons.mp hpw
    have hz := zeroOut_ok h.scr h.rdi h256 hp hl hpv hlv hl1 (by have := h.w2; omega) ⟨hwr, hsep⟩
    have step : ∀ s₁, ((∀ i < e.len, s₁.mem (e.out + BitVec.ofNat 64 i) = 0) ∧
        (∀ x, (∀ j < e.len, x ≠ e.out + BitVec.ofNat 64 j) → s₁.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s s₁) →
        WP isa (seqs (zerosK L ++ rest)) s₁ Q := by
      intro s₁ ⟨z₁, x₁, k₁⟩
      have f₁ := frm_scr hsep x₁
      have h₁ : Ws s₁ B Z w := h.congr f₁ (fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Or.inl (by omega)) k₁ (by decide)
      refine zeros_ok L rest s₁ hr h₁ (fun e' he' => ?_) hpw'.2
        (fun t ht ft zt xt kt => k t ht (Frm.trans f₁ ft) ?_ ?_ ((k₁.trans kt).mono (by simp)))
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
    have hne : zerosK L ++ rest ≠ [] := by simp [hr]
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
  have := L.pl8; simp only [KIn.W]; omega

theorem lt_of_os2ip_len {bs : List Byte} {n : Nat} (h : bs.length = n) : Spec.Rsa.os2ip bs < 2 ^ (8 * n) := by
  have := VG.Proof.Rsa.lt_of_os2ip bs
  rw [h, show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] at this
  exact this

/-- From the loads to `smallMask`. -/
theorem front_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) :
    WP isa (seqs ((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask))))))) s
      fun t => Front I m₀ t ∧ InScr I.B I.Z s.mem t.mem := by
  have hZ := h.hZ
  have hW := L.W
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  have hP₀ : I.P₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.pbl
  have hQ₀ : I.Q₀ < 2 ^ (64 * (I.pl / 8)) := by rw [← hw8]; exact lt_of_os2ip_len L.qbl
  have hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  -- The loads.
  refine wp_seqs_append (by simp [loadA]) (by simp [order, ltA]) (WP.mono (loads_k h L.pbl L.qbl L.ebl
    (by have := L.pl1; omega) (by rw [hW]; have := L.pl8; omega) L.el1 L.el8) fun s₁ ⟨h₁, f₁, vP₁, vQ₁, ev₁⟩ => ?_)
  -- The order.
  refine wp_seqs_append (by simp [order, ltA]) (by simp [decTo]) (WP.mono (order_k h₁) fun s₂ ⟨h₂, f₂, vP₂, vQ₂⟩ => ?_)
  rw [vP₁, vQ₁] at vP₂ vQ₂
  -- `p − 1`, `q − 1`.
  refine wp_seqs_append (by simp [decTo]) (by simp [decTo]) (WP.mono (decTo_k h₂ (o := aPm) (j := aPa) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, vPm₃, _⟩ => ?_)
  refine wp_seqs_append (by simp [decTo]) (by simp [lcmPart, phi]) (WP.mono (decTo_k h₃ (o := aQm) (j := aQa)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨h₄, f₄, vQm₄, _⟩ => ?_)
  have hok3 : [Rc.arr aPm, Rc.arr aC].all Rc.ok = true := by decide
  have hok4 : [Rc.arr aQm, Rc.arr aC].all Rc.ok = true := by decide
  have vP₄ : av I s₄.mem aPa = I.P := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vP₂]
  have vQ₄ : av I s₄.mem aQa = I.Q := by
    rw [f₄.av hok4 (by decide) (by decide) hZ, f₃.av hok3 (by decide) (by decide) hZ, vQ₂]
  rw [vP₂] at vPm₃
  rw [f₃.av hok3 (by decide) (by decide) hZ, vQ₂] at vQm₄
  have vPm₄ : av I s₄.mem aPm = I.P - 1 := by rw [f₄.av hok4 (by decide) (by decide) hZ, vPm₃]
  have hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.P, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega
  have hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    simp only [KIn.Q, KIn.P₀, KIn.Q₀] at hP₀ hQ₀ ⊢; split <;> omega
  -- `L`.
  refine wp_seqs_append (by simp [lcmPart, phi]) (by simp) (WP.mono (lcm_k h₄ hW vPm₄ vQm₄ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hPw)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hQw))
    fun s₅ ⟨h₅, f₅, vL₅⟩ => ?_)
  have hokL : [Rc.arr aL, Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR,
    Rc.hdr sMo, Rc.hdr kOk].all Rc.ok = true := by decide
  have hokE : [Rc.arr aPa, Rc.arr aQa, Rc.hdr kEv].all Rc.ok = true := by decide
  have ev₅ : word s₅.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₅.word hokL (by decide) (by decide), f₄.word hok4 (by decide) (by decide),
      f₃.word hok3 (by decide) (by decide), f₂.word (by decide) (by decide) (by decide), ev₁]
  have hLW : I.L < 2 ^ (64 * I.W) := by
    have h1 : I.L ≤ (I.P - 1) * (I.Q - 1) ∨ I.L = 0 := by
      rcases Nat.eq_zero_or_pos ((I.P - 1) * (I.Q - 1)) with h0 | h0
      · right; simp only [KIn.L]
        rcases Nat.mul_eq_zero.mp h0 with h' | h' <;> simp [h']
      · left; exact Nat.le_of_dvd h0 (Nat.lcm_dvd_mul _ _)
    have h2 : (I.P - 1) * (I.Q - 1) < 2 ^ (64 * I.W) := by
      rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega, Nat.pow_add]
      exact Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (Nat.two_pow_pos _)
    rcases h1 with h1 | h1
    · omega
    · rw [h1]; exact Nat.two_pow_pos _
  -- `d`.
  refine wp_seqs_append (by simp) (by simp [smallMask, constA]) ?_
  simp only [seqs]
  refine WP.mono (dPart_k h₅ hE ev₅ vL₅ hLW) fun s₆ ⟨h₆, f₆, d₆⟩ => ?_
  obtain ⟨ok, ok₆, iff₆, dd₆⟩ := d₆
  -- ZF.
  refine WP.mono (smallMask_k h₆ hW ok₆) fun t ⟨ht, f₇, zf₇⟩ => ?_
  have hokD : csD.all Rc.ok = true := by decide
  have hok7 : [Rc.arr aC].all Rc.ok = true := by decide
  have pres : ∀ j, j < 16 → Rc.arr j ∉ csD → Rc.arr j ∉ [Rc.arr aC] → Rc.arr j ∉ [Rc.arr aL, Rc.arr aU, Rc.arr aV,
      Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT, Rc.arr aR, Rc.hdr sMo, Rc.hdr kOk] →
      av I t.mem j = av I s₄.mem j := fun j hj h1 h2 h3 => by
    rw [f₇.av hok7 hj h2 hZ, f₆.av hokD hj h1 hZ, f₅.av hokL hj h3 hZ]
  have okt : word t.mem I.B (8 * kOk) = mask ok := by rw [f₇.word hok7 (by decide) (by decide), ok₆]
  have hD : av I t.mem aDd = av I s₆.mem aDd := f₇.av hok7 (by decide) (by decide) hZ
  have hi : InScr I.B I.Z s.mem t.mem := fun x hx => (ht.inScr x hx).trans (h.inScr x hx).symm
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ⟨ok, okt, iff₆, fun d hd => by rw [hD]; exact dd₆ d hd⟩,
    ⟨ok, okt, iff₆, by rw [zf₇, ← hD, show 64 * (I.pl / 8) = 8 * I.pl by omega]⟩⟩, hi⟩
  · rw [pres aPa (by decide) (by decide) (by decide) (by decide), vP₄]
  · rw [pres aQa (by decide) (by decide) (by decide) (by decide), vQ₄]
  · rw [pres aPm (by decide) (by decide) (by decide) (by decide), vPm₄]
  · rw [pres aQm (by decide) (by decide) (by decide) (by decide), vQm₄]
  · rw [f₇.word hok7 (by decide) (by decide), f₆.word hokD (by decide) (by decide), ev₅]

end VG.Proof.RsaKeyGen.X86_64.Key

end
