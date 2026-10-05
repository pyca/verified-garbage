import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Code
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase

/-!
# An RSA key from its primes on x86-64: constant time, the relation

Two runs agree on the public data (`KP`: the working space, the pointers
and lengths, `e` and the status). Between the pieces of the code, each run
is in a state `KS` describes for its own inputs, with the facts `F` the next
piece needs (`KG F`). A piece reloads `w` and the stride from the header
(`ws`) and computes the arrays' bases from them; the taint analysis checks
the rest of it from `rdi`, `r12` and `r9`, which correctness pins (`kg_ws`,
from `ws_ct`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- The public part of the inputs. -/
structure KQ where
  B : Addr
  Z : Nat
  pl : Nat
  pN : Addr
  pD : Addr
  pP : Addr
  pQ : Addr
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pE : Addr
  el : Nat
  eb : List Byte
  Wr : List Region
  sp : Addr

/-- The public data: the public inputs and the status. -/
structure KP where
  q : KQ
  st : Nat

def KIn.pub (I : KIn) : KQ := ⟨I.B, I.Z, I.pl, I.pN, I.pD, I.pP, I.pQ, I.pDp, I.pDq, I.pQi, I.pE, I.el, I.eb, I.Wr, I.sp⟩

/-- The status of the inputs. -/
abbrev KIn.st (I : KIn) : Nat := Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp I.pl I.eb I.pb I.qb)

/-- Between the pieces: the state of some inputs with the public data `p`,
with the facts `F`. -/
def KG (F : KIn → State → Prop) (p : KP) (s : State) : Prop :=
  ∃ I m₀, I.pub = p.q ∧ I.st = p.st ∧ KS I m₀ s ∧ KLens I ∧ KOuts I ∧ F I s

/-- No facts. -/
abbrev NF : KIn → State → Prop := fun _ _ => True

theorem KG.ws {F : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) :
    Ws s p.q.B p.q.Z (2 * p.q.pl / 8) := by
  obtain ⟨I, m₀, he, -, hk, -⟩ := h
  rw [← he]; exact hk.ws

theorem pins_kg (F : KIn → State → Prop) : Pins (KG F) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- `KG` with other facts. -/
theorem KG.imp {F G : KIn → State → Prop} {p : KP} {s : State} (h : KG F p s) (hFG : ∀ I, F I s → G I s) :
    KG G p s := by
  obtain ⟨I, m₀, he, hst, hk, L, O, hF⟩ := h
  exact ⟨I, m₀, he, hst, hk, L, O, hFG I hF⟩

/-- A piece from `KG F` to `KG G`, by what correctness gives from `KS`. -/
theorem kg_post {F G : KIn → State → Prop} {c : Prog isa}
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa c s fun t => KS I m₀ t ∧ G I t) :
    ∀ p s, KG F p s → WP isa c s (KG G p) := fun _ _ ⟨I, m₀, he, hst, hk, L, O, hF⟩ =>
  WP.mono (hw I m₀ _ hk L hF) fun _ ⟨hk', hG⟩ => ⟨I, m₀, he, hst, hk', L, O, hG⟩

/-- `ws` and then code the taint analysis checks from `rdi`, `r12` and
`r9`. -/
theorem kg_ws {F G : KIn → State → Prop} {rest : List Instr} {body : Prog isa}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s →
      WP isa (.seq (.block (ws ++ rest)) body) s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.seq (.block (ws ++ rest)) body) (Two (KG G)) :=
  ws_ct (fun p : KP => p.q.B) (fun p => p.q.Z) (fun p => 2 * p.q.pl / 8) (fun _ _ h => h.ws) ht (kg_post hw)

/-- `kg_ws` for a block. -/
theorem kg_wsb {F G : KIn → State → Prop} {rest : List Instr} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa (.block (ws ++ rest)) s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block (ws ++ rest)) (Two (KG G)) :=
  ws_block_ct (fun p : KP => p.q.B) (fun p => p.q.Z) (fun p => 2 * p.q.pl / 8) (fun _ _ h => h.ws) ht (kg_post hw)

/-- Code the taint analysis checks from `rdi` alone. -/
theorem kg_rdi {F G : KIn → State → Prop} {c : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) c hc).isSome = true)
    (hw : ∀ I m₀ s, KS I m₀ s → KLens I → F I s → WP isa c s fun t => KS I m₀ t ∧ G I t) :
    RelCT isa (Two (KG F)) c (Two (KG G)) :=
  two_piece [.rdi] (pins_kg F) ht (kg_post hw)

/-- A sequence in two parts, each constant time. -/
theorem rs_app {P R Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h₁ : RelCT isa P (seqs a) R) (h₂ : RelCT isa R (seqs b) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  RelCT.seqs_app ha hb (RelCT.seq h₁ h₂)

/-- Facts that survive a piece which changes the parts `cs` and keeps the
registers outside `rs`. -/
def Stab (F : KIn → State → Prop) (cs : List Rc) (rs : List Reg) : Prop :=
  ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → KF I.B I.W cs s.mem t.mem → Keep rs s t → F I t

theorem kf_eq {B : Addr} {W : Nat} {cs : List Rc} {m m' : Mem} (hm : m' = m) : KF B W cs m m' := by
  rw [hm]; exact (KF.refl _ _ _).mono (by simp)

theorem stab_nf (cs : List Rc) (rs : List Reg) : Stab NF cs rs := fun _ _ _ _ _ _ _ => trivial

theorem Stab.mono {F : KIn → State → Prop} {cs cs' : List Rc} {rs rs' : List Reg} (h : Stab F cs rs)
    (hc : ∀ c ∈ cs', c ∈ cs) (hr : ∀ r ∈ rs', r ∈ rs) : Stab F cs' rs' :=
  fun I s t hZ hF hf k => h I s t hZ hF (hf.mono hc) ⟨fun r hr' => k.1 r fun h => hr' (hr r h), k.2⟩

/-- `e`'s value in its header slot. -/
abbrev EvOK : KIn → State → Prop := fun I t => word t.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E

theorem stab_ev {cs : List Rc} (rs : List Reg) (hok : cs.all Rc.ok = true) (hn : .hdr kEv ∉ cs) :
    Stab EvOK cs rs := fun _ _ _ _ hF hf _ => (hf.word hok (by decide) hn).trans hF

theorem stab_and {F G : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (hF : Stab F cs rs)
    (hG : Stab G cs rs) : Stab (fun I t => F I t ∧ G I t) cs rs :=
  fun I s t hZ ⟨a, b⟩ hf k => ⟨hF I s t hZ a hf k, hG I s t hZ b hf k⟩

/-- The registers a piece may change: all but `rdi` and `rsp`. -/
abbrev allR : List Reg := [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem Stab.sub {F : KIn → State → Prop} {cs : List Rc} {rs : List Reg} (h : Stab F cs allR)
    (hr : ∀ r ∈ rs, r ∈ allR := by decide) : Stab F cs rs :=
  h.mono (fun _ h => h) hr

theorem stab_r15 {cs : List Rc} {rs : List Reg} (h : .r15 ∉ rs) :
    Stab (fun _ t => ∃ c, t.gpr .r15 = mask c) cs rs := fun _ _ _ _ ⟨c, hc⟩ _ k => ⟨c, (k.gpr h).trans hc⟩

theorem stab_rbp {cs : List Rc} {rs : List Reg} (h : .rbp ∉ rs) :
    Stab (fun _ t => ∃ c, t.gpr .rbp = mask c) cs rs := fun _ _ _ _ ⟨c, hc⟩ _ k => ⟨c, (k.gpr h).trans hc⟩

/-- `KS` after a piece that changes no memory. -/
theorem KS.same {I : KIn} {m₀ : Mem} {s t : State} (h : KS I m₀ s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hr : .rdi ∉ rs ∧ .rsp ∉ rs) : KS I m₀ t :=
  h.step (cs := []) (by rw [hm]; exact KF.refl _ _ _) rfl k hr

/-- A block of the registers alone, checked by the taint analysis from `rdi`. -/
theorem kg_regs {F G : KIn → State → Prop} {l : List Instr} {rs : List Reg} (hr : .rdi ∉ rs ∧ .rsp ∉ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (ht : (taint.check (Taint.ofRegs [.rdi]) (.block l) hc).isSome = true)
    (hw : ∀ I s, slot I.W 16 ≤ 2 ^ 64 → F I s → WP isa (.block l) s fun t => t.mem = s.mem ∧ Keep rs s t ∧ G I t) :
    RelCT isa (Two (KG F)) (.block l) (Two (KG G)) :=
  kg_rdi ht fun I _ s h _ hf => WP.mono (hw I s h.hZ hf) fun _ ⟨hm, k, hg⟩ => ⟨h.same hm k hr, hg⟩

/-! ## The pieces of the key routines -/

theorem zeroA_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16)
    (hF : Stab F [.arr j] [.r12, .r9, .r8, .rax, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (KG F)) (zeroA j) (Two (KG F)) :=
  kg_ws ht fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun _ ⟨ht, f, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

theorem copyA_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (hF : Stab F [.arr o] [.r12, .r9, .rsi, .rbx, .rax, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rsi ++ base o .rbx)) Impl.Rsa.X86_64.copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (copyA o a) (Two (KG F)) := by
  have e : copyA o a = .seq (.block (ws ++ (base a .rsi ++ base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [copyA, List.append_assoc]
  rw [e]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← e]
    exact WP.mono (copyA_k h ho ha hoa) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

end VG.Proof.RsaKeyGen.X86_64.Key
