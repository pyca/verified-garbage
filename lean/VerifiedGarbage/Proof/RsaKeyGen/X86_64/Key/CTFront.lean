import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Res
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Main
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Entry
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Implies
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT

/-! ## Code -/
section

/-!
# An RSA key from its primes on x86-64: correctness

`code`, from a state `keyCtr` allows, ends as `keyOp` (`keyCode_wp`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

theorem code_eq : code = seqs (([.block (entry ++ head)] : List (Prog isa)) ++
    (((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask)))))) ++
    ([.ite .ne (zeros 2) keyPart] : List (Prog isa)))) := by
  simp only [code, List.append_assoc]

/-- The working space set up: `KS` from the state on entry, after `entry`
and `head`. -/
theorem keyStart_k {s : State} (c : KCtx s) :
    WP isa (.block (entry ++ head)) s fun t => KS (keyIn s) s.mem t := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have L := c.L
  have hpl : (keyIn s).pl = (s.gpr .r9).toNat := rfl
  have hpl1 := L.pl1
  have hpl2 := L.pl2
  have h256 : 8 * 32 ≤ (arg s 11).toNat * 8 := by
    have : 8 * 32 ≤ slot (keyIn s).W 16 := by unfold slot hdrBytes; omega
    omega
  rw [WP.block_append_iff]
  refine WP.mono (keyEntry_ok rfl (fun i hi => hs.st (by omega)) c.ha c.hsep) fun t₁ he => ?_
  have hs₁ := hs.congr he.keep.2.2
  have hnl : word t₁.mem (arg s 10) (8 * kNl) = BitVec.ofNat 64 (2 * (s.gpr .r9).toNat) := by
    rw [he.nl]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, c.rsi]; omega)
  refine WP.mono (keyHead_ok hs₁ he.rdi hnl (by omega) (by omega) hZ) fun t₂ ⟨hw₂, hf₂, k₂⟩ => ?_
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have hi₁ : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₁.mem := InScr.of_outside he.frame (by omega)
  have hi₂ : InScr (arg s 10) ((arg s 11).toNat * 8) t₁.mem t₂.mem := InScr.of_frm hf₂ (by
    have : 8 * sStride + 8 ≤ slot (keyIn s).W 16 := by rw [eS]; unfold slot hdrBytes; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega)
  have hi := hi₁.trans hi₂
  have hrd : t₂.rd = s.rd := k₂.2.1.trans he.keep.2.1
  have hwr : t₂.wr = s.wr := k₂.2.2.trans he.keep.2.2
  have hA₁ : KArgs t₁.mem (keyIn s) :=
    ⟨he.no, hnl, he.dd, he.pp, he.pl.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.qp, he.dp, he.dq, he.qi, he.e,
      he.el.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.saved⟩
  refine ⟨hw₂, hA₁.congr fun i hi' => hf₂.word_eq (fun r hr => ?_) (by omega), c.p.congr hi hrd hwr,
    c.q.congr hi hrd hwr, c.e.congr hi hrd hwr, hi, hwr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · exact (k₂.gpr (by decide)).trans (he.keep.gpr (by decide))

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t₃ t : State} (c : KCtx s) (hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem)
    (R : OutsRes (keyIn s) t.mem (t.gpr .rax)) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (keyIn s).sv i)
    (hf : ∀ y, (keyIn s).Z ≤ ofs (keyIn s).B y →
      (∀ o ∈ outsL (keyIn s), ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = t₃.mem y)
    (hsp : t.gpr .rsp = (keyIn s).sp) :
    gprPreserved s t ∧ keyPost s t := by
  have ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.rsi]
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZb, hnb⟩ := c.hret b (by omega)
    rw [hf _ hZb hnb, hi _ hZb]
  · unfold keyPost keyRes
    rw [ho]
    exact R

/-- `code` computes `keyOp`. -/
theorem keyCode_wp (s : State) (h : keyPre s) : WP isa code s fun t => gprPreserved s t ∧ keyPost s t := by
  have c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (front_k k₁ c.L) fun t₃ ⟨F, hi₃⟩ => ?_)
  obtain ⟨ok, hok, hiff, hzf⟩ := F.zf
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  have hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem := k₁.inScr.trans hi₃
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok') (by simp [eval, hzf])
    (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    have hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      keyPost_of c hi (outsRes_zeros hd hsm Z) Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    have R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, hsv, hf, hsp⟩ := T
    exact keyPost_of c hi R hsv hf hsp

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTBase -/
section

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
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

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

end

/-! ## CTUnits -/
section

/-!
# An RSA key from its primes on x86-64: constant time, the key routines

Each of `constA`, `ltA`, `eqMask`, `selC`, `subC`, `setOneA`, `divmod` and
`inverse` leaks the same from two runs in `KG F` and leaves `KG F`, for
facts `F` its changes keep (`Stab`); `selC`, `subC`, `setOneA` and
`inverse` need the facts their correctness needs.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `constA`'s store of `x`. -/
theorem constBlk_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (x : BitVec 32) :
    WP isa (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) s
      fun t => KS I m₀ t ∧ KF I.B I.W [.arr aC] s.mem t.mem ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.ws.scr.nowrap
  have sC := h.ws.sl (j := aC) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₂ ⟨_, h9, m₂, k₂⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aC (r := .rbx) (by decide) ((k₂.gpr (by decide)).trans h.ws.rdi) h9)
    fun s₃ ⟨hbx, m₃, k₃⟩ => ?_
  have hs₃ := h.ws.scr.congr (k₂.trans k₃).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off I.B (slot I.W aC)) (x.setWidth 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₃.st (d := slot I.W aC) (by omega), m₃, m₂]) rfl) fun t ⟨hm, k₄⟩ => ?_
  have o₄ := writeW_outside s.mem I.B (x.setWidth 64) (d := slot I.W aC) (by omega)
  rw [← hm] at o₄
  have f₄ := KF.arr1 (j := aC) o₄ (Nat.le_refl _) (by omega)
  have kk := (k₂.trans k₃).trans k₄
  exact ⟨h.step f₄ (all_mut_arr (by decide)) kk (by decide), f₄, kk.mono (by simp)⟩

theorem constA_ct {F : KIn → State → Prop} (x : BitVec 32) (hF : Stab F [.arr aC] [.r12, .r9, .r8, .rax, .r14, .rbx])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (constA x)) (Two (KG F)) := by
  have e : seqs (constA x) = .seq (zeroA aC)
      (.block (ws ++ (base aC .rbx ++ ([.mov32 .rax (.imm x), .store (at0 .rbx) .rax] : List Instr)))) := by
    simp only [constA, seqs, List.append_assoc]
  rw [e]
  exact RelCT.seq (zeroA_ct (by decide) (hF.mono (by simp) (by simp)) ht₁)
    (kg_wsb ht₂ fun I _ s h _ hf => WP.mono (constBlk_k h x) fun _ ⟨ht, f, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp))⟩)

theorem ltA_eq (a b : Nat) : seqs (ltA a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]) := by
  simp only [ltA, seqs, List.append_assoc]

theorem ltA_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a < av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))
      (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]))
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (ltA a b)) (Two (KG G)) := by
  rw [ltA_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← ltA_eq]
    exact WP.mono (ltA_k h ha hb) fun _ ⟨ht, hm, hbp, _, _, _, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

theorem eqMask_eq (a b : Nat) : seqs (eqMask a b) = .seq (.block (ws ++ (base a .rbx ++ (base b .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr))))) (.seq (wordLoop 0 xorBody) (.block isZero)) := by
  simp only [eqMask, eqA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem eqMask_ct {F G : KIn → State → Prop} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → t.mem = s.mem → Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t →
      t.gpr .rbp = mask (decide (av I s.mem a = av I s.mem b)) → G I t)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .rbx ++ (base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (eqMask a b)) (Two (KG G)) := by
  rw [eqMask_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← eqMask_eq]
    exact WP.mono (eqMask_k h ha hb) fun _ ⟨ht, hm, hbp, k⟩ => ⟨ht, hFG I s _ h.hZ hf hm k hbp⟩

/-- A mask in `rbp`. -/
abbrev RbpM : KIn → State → Prop := fun _ t => ∃ c, t.gpr .rbp = mask c

/-- A mask in `r15`. -/
abbrev R15M : KIn → State → Prop := fun _ t => ∃ c, t.gpr .r15 = mask c

theorem selC_eq (j : Nat) : seqs (selC j) = .seq (.block (ws ++ (base j .r8 ++ base aC .rsi))) (wordLoop 0 selBody) := by
  simp only [selC, seqs, List.append_assoc]

theorem selC_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjC : j ≠ aC)
    (hF : Stab F [.arr j] [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14]) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base aC .rsi))
      (wordLoop 0 selBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ RbpM I t)) (seqs (selC j)) (Two (KG F)) := by
  rw [selC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, hbp⟩ => by
    rw [← selC_eq]
    exact WP.mono (selC_k h hj hjC hbp) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

theorem subC_eq (o a : Nat) : seqs (subC o a) = .seq (.block (ws ++ (base a .r8 ++ (base aC .r10 ++ (base o .rsi ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))) (wordLoop 0 subMBody) := by
  simp only [subC, seqs, List.append_assoc]

theorem subC_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoC : o ≠ aC) (haC : a ≠ aC)
    (hoa : o = a ∨ o ≠ a) (hF : Stab F [.arr o] [.r12, .r9, .r8, .r10, .rsi, .rbp, .rax, .rdx, .r14])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ R15M I t)) (seqs (subC o a)) (Two (KG F)) := by
  rw [subC_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, c, h15⟩ => by
    rw [← subC_eq]
    exact WP.mono (subC_k h ho ha hoC haC hoa h15) fun _ ⟨ht, f, _, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- Array `j` zero. -/
abbrev Zero (j : Nat) : KIn → State → Prop := fun I t => wv t.mem I.B (slot I.W j) (I.W + 2) = 0

theorem setOneA_eq (j : Nat) : setOneA j = ws ++ (base j .rbx ++
    ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr)) := by
  simp only [setOneA, List.append_assoc]

theorem setOne_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .rbx, .rax])
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ Zero j I t)) (.block (setOneA j)) (Two (KG F)) := by
  rw [setOneA_eq]
  exact kg_wsb ht fun I _ s h _ ⟨hf, hz⟩ => by
    rw [← setOneA_eq]
    exact WP.mono (setOne_k h hj hz) fun _ ⟨ht, f, _, k⟩ => ⟨ht, hF I s _ h.hZ hf f k⟩

/-- `zeroA j` then `setOneA j`. -/
theorem one_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hF : Stab F [.arr j] [.r12, .r9, .r8, .rbx, .rax, .r14])
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++
      ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (.seq (zeroA j) (.block (setOneA j))) (Two (KG F)) :=
  RelCT.seq (kg_ws ht₁ fun I _ s h _ hf => WP.mono (zeroA_k h hj) fun _ ⟨ht, f, hz, k⟩ =>
      ⟨ht, hF I s _ h.hZ hf f (k.mono (by simp)), hz⟩)
    (setOne_ct hj (hF.mono (by simp) (by simp)) ht₂)

/-- The registers `divmod` and `inverse` may change. -/
abbrev dvRegs : List Reg := List.filter (· != .rdi) (.r9 :: .r11 :: stepRegs)

theorem divmod_eq (iQ iR iD iT : Nat) : divmod iQ iR iD iT = .seq (.block (ws ++ (base iR .r8 ++
    (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    ([.mov32 .r13 (.imm 0)] : List Instr))))))
    (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne)) := by
  simp only [divmod, divInit, seqs, List.append_assoc]

theorem divmod_ct {F : KIn → State → Prop} {iQ iR iD iT : Nat} (hQ : iQ < 16) (hR : iR < 16) (hD : iD < 16)
    (hT : iT < 16) (dQR : iQ ≠ iR) (dQD : iQ ≠ iD) (dQT : iQ ≠ iT) (dRD : iR ≠ iD) (dRT : iR ≠ iT) (dDT : iD ≠ iT)
    (hF : Stab F [.arr iQ, .arr iR, .arr iT] dvRegs) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base iR .r8 ++
      (([.mov .r11 (.reg .r12)] : List Instr) ++ (List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
      ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep iQ iR iD iT) .ne))) hc).isSome = true) :
    RelCT isa (Two (KG F)) (divmod iQ iR iD iT) (Two (KG F)) := by
  rw [divmod_eq]
  exact kg_ws ht fun I _ s h _ hf => by
    rw [← divmod_eq]
    refine WP.mono (divmod_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hQ hR hD
      hT dQR dQD dQT dRD dRT dDT) fun t ⟨hdi, hf', k, _⟩ => ?_
    have f : KF I.B I.W [.arr iQ, .arr iR, .arr iT] s.mem t.mem := hf'
    have k' : Keep dvRegs s t :=
      ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
        ⟨hm, by simp [e]⟩), k.2⟩
    exact ⟨h.step f (all_mut_arrs (js := [iQ, iR, iT]) (by simp [hQ, hR, hT])) k' (by decide), hF I s t h.hZ hf f k'⟩

/-- `inverse`'s start, for `u`, `v`, `x₁`, `x₂` and the modulus `m`. -/
abbrev InvS (iU iV iX₁ iX₂ iM : Nat) : KIn → State → Prop := fun I t =>
  atop I t.mem iU = 0 ∧ av I t.mem iV = av I t.mem iM ∧ av I t.mem iX₁ = 1 ∧ av I t.mem iX₂ = 0

theorem inverse_eq (iU iV iX₁ iX₂ iM iT : Nat) : inverse iU iV iX₁ iX₂ iM iT =
    .seq (.block (ws ++ (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr)))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) .ne) := by
  simp only [inverse, invInit, List.append_assoc]

theorem inverse_ct {F : KIn → State → Prop} {iU iV iX₁ iX₂ iM iT : Nat}
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT)
    (hF : Stab F [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] dvRegs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.mov .r11 (.reg .r12)] : List Instr) ++
      (List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ ([.mov32 .r13 (.imm 0)] : List Instr))))
      (.loop (VG.Impl.Rsa.X86_64.Keys.invStep iU iV iX₁ iX₂ iM iT) .ne)) hc).isSome = true) :
    RelCT isa (Two (KG fun I t => F I t ∧ InvS iU iV iX₁ iX₂ iM I t)) (inverse iU iV iX₁ iX₂ iM iT)
      (Two (KG F)) := by
  rw [inverse_eq]
  exact kg_ws ht fun I _ s h _ ⟨hf, hU0, hVM, hX1, hX2⟩ => by
    rw [← inverse_eq]
    refine WP.mono (inverse_ok h.ws.scr h.ws.rdi h.ws.hw h.ws.hS (by have := h.ws.w1; omega) h.ws.w2 h.ws.hZ hU hV
      hX₁ hX₂ hM hT dUV dUX₁ dUX₂ dUM dUT dVX₁ dVX₂ dVM dVT dX dX₁M dX₁T dX₂M dX₂T dMT hU0 hVM hX1 hX2)
      fun t ⟨hdi, hf', k, _⟩ => ?_
    have f : KF I.B I.W [.arr iU, .arr iV, .arr iX₁, .arr iX₂, .arr iT, .hdr sMo] s.mem t.mem :=
      KF.of_frm hf' fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨.arr iU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₁, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iX₂, by simp, by simp [Rc.range], by simp only [Rc.range]; omega⟩
        · exact ⟨.arr iT, by simp, by simp [Rc.range], by simp [Rc.range]⟩
        · exact ⟨.hdr sMo, by simp, by simp [Rc.range], by simp [Rc.range]⟩
    have k' : Keep dvRegs s t :=
      ⟨fun r hr => if e : r = .rdi then by rw [e, hdi, h.ws.rdi] else k.1 r fun hm => hr (List.mem_filter.mpr
        ⟨hm, by simp [e]⟩), k.2⟩
    refine ⟨h.step f ?_ k' (by decide), hF I s t h.hZ hf f k'⟩
    simp only [List.all_cons, List.all_nil, Rc.mut, sMo, sFn, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

end VG.Proof.RsaKeyGen.X86_64.Key

end

/-! ## CTFront -/
section

/-!
# An RSA key from its primes on x86-64: constant time, the loads, the order and `p − 1`, `q − 1`

The loads take the pointer and the length from the header, which correctness
pins to the public data (`loadA_ct`, `loadE_ct`); the rest are pieces of
the key routines.
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

/-- `loadA`'s block and `loadBE`, from `KS`. -/
theorem loadTail_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) {j sPtr sLen len : Nat} {ptr : Addr}
    {bs : List Byte} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (hp : word s.mem I.B (8 * sPtr) = ptr)
    (hl : word s.mem I.B (8 * sLen) = BitVec.ofNat 64 len) (hsrc : Src s I.B I.Z ptr bs) (hbl : bs.length = len)
    (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W) :
    WP isa (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] :
      List Instr))) loadBE) s fun t => KS I m₀ t ∧ KF I.B I.W [.arr j] s.mem t.mem ∧ Keep allR s t := by
  have hw := h.ws
  have hn := hw.scr.nowrap
  have sj := hw.sl hj
  have hw2 := hw.w2
  refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
  have ht := h.same hm k (by decide)
  have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
    (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
    (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ => ?_
  rw [hm] at o
  have f := KF.arr1 (I := I) (j := j) o (Nat.le_refl _) (by omega)
  exact ⟨h.step f (all_mut_arr hj) (k.trans k') (by decide), f, (k.trans k').mono (by decide)⟩

theorem loadA_eq (j sPtr sLen : Nat) : seqs (loadA j sPtr sLen) = .seq (zeroA j)
    (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)), .mov .rcx (.mem (hdr sLen))] : List Instr)))
      loadBE) := by
  simp only [loadA, seqs]

/-- `loadA j sPtr sLen` for the number whose pointer and length (functions of
the public inputs) are in the header slots `sPtr` and `sLen`. -/
theorem loadA_ct {F : KIn → State → Prop} {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : KQ → Addr) (len : KQ → Nat)
    (hA : ∀ I m₀ s, KS I m₀ s → KLens I → word s.mem I.B (8 * sPtr) = ptr I.pub ∧
      word s.mem I.B (8 * sLen) = BitVec.ofNat 64 (len I.pub) ∧
      (∃ bs, Src s I.B I.Z (ptr I.pub) bs ∧ bs.length = len I.pub) ∧ 1 ≤ len I.pub ∧ len I.pub ≤ 8 * I.W)
    (hF : Stab F [.arr j] allR) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rdi, .rbx, .rsi, .rcx]) loadBE hc₃).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (loadA j sPtr sLen)) (Two (KG F)) := by
  rw [loadA_eq]
  refine RelCT.seq (zeroA_ct hj (hF.mono (fun _ h => h) (by decide)) ht₁) ?_
  refine pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx]
    (fun p : KP => ioVal p.q.B (off p.q.B (slot (2 * p.q.pl / 8) j)) (ptr p.q) (len p.q)) (pins_kg F) ht₂ ?_ ht₃ ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hp, hl, -⟩ := hA I m₀ s hk L
    exact WP.mono (loadBlk_ok hk.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hdi
      · exact hbx
      · exact hsi
      · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, hf⟩
    obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA I m₀ s hk L
    exact WP.mono (loadTail_k hk hj hP hL hp hl hsrc hbl hl1 hlw) fun t ⟨ht, f, k⟩ =>
      ⟨I, m₀, rfl, rfl, ht, L, O, hF I s t hk.hZ hf f k⟩

theorem loadAP_ct : RelCT isa (Two (KG NF)) (seqs (loadA aPa kPp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pP KQ.pl
    (fun I _ _ h L => ⟨h.args.pp, h.args.pl, ⟨_, h.p, L.pbl⟩, show 1 ≤ I.pl by have := L.pl1; omega,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

theorem loadAQ_ct : RelCT isa (Two (KG NF)) (seqs (loadA aQa kQp kPl)) (Two (KG NF)) :=
  loadA_ct (by decide) (by decide) (by decide) KQ.pQ KQ.pl
    (fun I _ _ h L => ⟨h.args.qp, h.args.pl, ⟨_, h.q, L.qbl⟩, show 1 ≤ I.pl by have := L.pl1; omega,
      show I.pl ≤ 8 * I.W by rw [L.W]; have := L.pl8; omega⟩)
    (stab_nf _ _) (by taint_decide) (by taint_decide) (by taint_decide)

/-- `e`'s pointer and length. -/
def eVal (pE : Addr) (el : Nat) : Reg → BitVec 64
  | .rsi => pE
  | .rcx => BitVec.ofNat 64 el
  | _ => 0

theorem loadE_eq : seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa))) =
    .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)), .mov32 .rbx (.imm 0)])
      (.seq (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) (.block [.store (hdr kEv) .rbx])) := rfl

/-- `e`'s load and its store into `kEv`. -/
theorem loadE_ct : RelCT isa (Two (KG NF)) (seqs (loadE ++ ([.block [.store (hdr kEv) .rbx]] : List (Prog isa)))) (Two (KG EvOK)) := by
  rw [loadE_eq]
  refine pin_ct [.rdi] [.rdi, .rsi, .rcx]
    (fun p : KP => fun r => if r = .rdi then p.q.B else eVal p.q.pE p.q.el r) (pins_kg NF) (by taint_decide) ?_
    (by taint_decide) ?_
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi =>
      hk.ws.scr.ld (by have := hk.ws.h256; omega)
    refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = I.pE ∧
        t.gpr .rcx = BitVec.ofNat 64 I.el) (by
      xrun [State.ea, hdr, hk.ws.rdi, hdrOff, hl kE (by decide), hl kElen (by decide), hk.args.e, hk.args.el]) rfl)
      fun t ⟨⟨hsi, hcx⟩, k⟩ r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (k.gpr (by decide)).trans hk.ws.rdi
    · exact hsi
    · exact hcx
  · rintro ⟨q, st⟩ s ⟨I, m₀, rfl, rfl, hk, L, O, -⟩
    obtain ⟨hg, hZ8⟩ := hk.ws.good
    have e₁ := loadE_ok hg hZ8 hk.args.e (by rw [hk.args.el, L.ebl]) (by rw [L.ebl]; exact L.el1)
      (by rw [L.ebl]; exact L.el8) hk.e
    rw [show seqs loadE = .seq (.block [.mov .rsi (.mem (hdr kE)), .mov .rcx (.mem (hdr kElen)),
      .mov32 .rbx (.imm 0)]) (.loop (.block [.shift .ror .rbx 56, .movzx8 .rax (at0 .rsi), .alu .add .rbx (.reg .rax),
        .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) from rfl] at e₁
    refine WP.assoc (WP.seq (WP.mono e₁ fun s₃ ⟨hbx, m₃, k₃⟩ => ?_))
    have h₃ := hk.same m₃ k₃ (by decide)
    have hst := h₃.ws.scr.st (d := 8 * kEv) (by have := h₃.ws.h256; unfold kEv sFn; omega)
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₃.mem.writeW (off I.B (8 * kEv))
      (BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb))) (by
        have hbx' : s₃.gpr .rbx = BitVec.ofNat 64 (Spec.Rsa.os2ip I.eb) := by
          rw [← hbx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        xrun [State.ea, hdr, h₃.ws.rdi, hdrOff, hst, hbx']) rfl) fun t ⟨hm, k₄⟩ => ?_
    obtain ⟨ht, -, hw⟩ := h₃.hdrW (i := kEv) (by unfold kEv sFn; omega) hm k₄ (by decide)
    exact ⟨I, m₀, rfl, rfl, ht, L, O, hw⟩

theorem order_eq : seqs order = .seq (.block (ws ++ (base aPa .rbx ++ (base aQa .r10 ++
    ([.mov32 .rbp (.imm 0)] : List Instr)))))
    (.seq (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp])
      (.seq (.block [.mov .r15 (.reg .rbp)]) (wordLoop 0 cswapBody))) := by
  simp only [order, ltA, seqs, List.append_assoc, List.cons_append, List.nil_append]

theorem order_ct : RelCT isa (Two (KG EvOK)) (seqs order) (Two (KG EvOK)) := by
  rw [order_eq]
  exact kg_ws (by taint_decide) fun I _ s h _ hf => by
    rw [← order_eq]
    exact WP.mono (order_k h) fun _ ⟨ht, f, _, _⟩ => ⟨ht, (f.word (by decide) (by decide) (by decide)).trans hf⟩

/-- `rbp`'s mask, negated, into `r15`. -/
theorem negR15_ok {s : State} {c : Bool} (h : s.gpr .rbp = mask c) :
    WP isa (.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) s fun t =>
      t.mem = s.mem ∧ Keep [.r15] s t ∧ t.gpr .r15 = mask (!c) := by
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = mask (!c) ∧ t.mem = s.mem)
    (by xrun [h, sxM1, maskNot]) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨hm, k, h15⟩

theorem decTo_eq (o j : Nat) : decTo o j = [zeroA o, copyA o j] ++ (constA 0 ++ (eqMask j aC ++
    (([.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] : List (Prog isa)) ++ (constA 1 ++ subC o o)))) := by
  simp only [decTo, subC, List.append_assoc]

/-- `decTo o j`, for facts that its changes keep. -/
theorem decTo_ct {F : KIn → State → Prop} {o j : Nat} (ho : o < 16) (hj : j < 16) (hoj : o ≠ j) (hoC : o ≠ aC)
    (hF : Stab F [.arr o, .arr aC] allR)
    {h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8)) zeroAccLoop) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base o .rbx))
      Impl.Rsa.X86_64.copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base aC .r8)) zeroAccLoop) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 0), .store (at0 .rbx) .rax] : List Instr))) h₄).isSome = true)
    (t₅ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (base aC .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr)))) (.seq (wordLoop 0 xorBody) (.block isZero))) h₅).isSome = true)
    (t₆ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]) h₆).isSome = true)
    (t₇ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.block (base aC .rbx ++ ([.mov32 .rax (.imm 1), .store (at0 .rbx) .rax] : List Instr))) h₇).isSome = true)
    (t₈ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base o .r8 ++ (base aC .r10 ++
      (base o .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 subMBody)) h₈).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (decTo o j)) (Two (KG F)) := by
  rw [decTo_eq]
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [zeroA o, copyA o j]) _ from
    RelCT.seq (zeroA_ct ho (hF.mono (by simp) (by decide)) t₁) (copyA_ct ho hj hoj (hF.mono (by simp) (by decide)) t₂)) ?_
  refine rs_app (by simp [constA]) (by simp [eqMask, eqA]) (constA_ct 0 (hF.mono (by simp) (by decide)) t₃ t₄) ?_
  refine rs_app (by simp [eqMask, eqA]) (by simp) (eqMask_ct (G := fun I t => F I t ∧ RbpM I t) hj
    (by decide) (fun I s t hZ hf hm k hbp => ⟨hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp))
      (k.mono (by decide)), _, hbp⟩) t₅) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [.mov .r15 (.reg .rbp),
      .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]]) _ from
    kg_regs (G := fun I t => F I t ∧ R15M I t) (by decide) t₆ fun I s hZ ⟨hf, c, hbp⟩ => WP.mono (negR15_ok hbp) fun t ⟨hm, k, h15⟩ =>
      ⟨hm, k, hF I s t hZ hf (by rw [hm]; exact KF.refl _ _ _ |>.mono (by simp)) (k.mono (by decide)), _, h15⟩) ?_
  refine rs_app (by simp [constA]) (by simp [subC]) (constA_ct 1
    (stab_and (hF.mono (by simp) (by decide)) (stab_r15 (by decide))) t₃ t₇) ?_
  exact subC_ct ho ho hoC hoC (.inl rfl) (hF.mono (by simp) (by decide)) t₈

theorem decP_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aPm aPa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

theorem decQ_ct : RelCT isa (Two (KG EvOK)) (seqs (decTo aQm aQa)) (Two (KG EvOK)) :=
  decTo_ct (by decide) (by decide) (by decide) (by decide) (stab_ev _ (by decide) (by decide))
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.X86_64.Key

end
