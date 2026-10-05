import VerifiedGarbage.Proof.Rsa.X86_64.RpMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTCode

/-!
# `vg_rsa_recover_primes` on x86-64: constant time, the prefix

`RpP`: the public data of `vg_rsa_recover_primes` (the working space, the
pointers and lengths, `n` and `e`, and the number of candidates tried).
`GA p`: what holds between the pieces of `main` (`RpS`), for the public
data `p`. The head, the loads, `-n⁻¹`, `M = d e` and the check of `M` leak
the same in two runs from `GM p` (`prefix_ct`), and leave the check's
result, which the public number of tries fixes (`prefixP_ct`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- The public data of `vg_rsa_recover_primes`. -/
structure RpP where
  B : Addr
  Z : Nat
  k : Nat
  el : Nat
  dl : Nat
  pP : Addr
  pQ : Addr
  pN : Addr
  pE : Addr
  pD : Addr
  nb : List Byte
  eb : List Byte
  W : List Region
  sp : Addr
  cnt : Nat
  deriving Inhabited

/-- The public part of the inputs. -/
def RpIn.pub (I : RpIn) : RpP :=
  ⟨I.B, I.Z, I.k, I.el, I.dl, I.pP, I.pQ, I.pN, I.pE, I.pD, I.nb, I.eb, I.W, I.sp,
    (Spec.Rsa.primesKey I.nb I.eb I.db).2⟩

/-- The outputs: writable, outside the working space, and apart. -/
structure RpOuts (I : RpIn) : Prop where
  p : ∀ i < I.k, InRegions I.W (I.pP + BitVec.ofNat 64 i) 1
  q : ∀ i < I.k, InRegions I.W (I.pQ + BitVec.ofNat 64 i) 1
  sp : ∀ i < I.k, I.Z ≤ ofs I.B (I.pP + BitVec.ofNat 64 i)
  sq : ∀ i < I.k, I.Z ≤ ofs I.B (I.pQ + BitVec.ofNat 64 i)
  a : Apart I.pP I.k I.pQ I.k

theorem RpPre.outs {I : RpIn} {s : State} (h : RpPre I s) : RpOuts I :=
  ⟨fun i hi => by rw [← h.wr]; exact h.oP.wr i hi, fun i hi => by rw [← h.wr]; exact h.oQ.wr i hi,
    h.oP.sep, h.oQ.sep, h.a⟩

/-- On entry to `main`. -/
def GM (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, I.pub = p ∧ RpPre I s ∧ Spec.Rsa.modulusValid I.N I.k = true

/-- Between the pieces of `main`. -/
def GA (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true

theorem GA.ws {p : RpP} {s : State} (h : GA p s) : Ws s p.B p.Z (wk p.k) := by
  obtain ⟨I, m₀, rfl, h, -⟩ := h
  exact h.ws

theorem pins_GA : Pins GA [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

theorem pins_GM : Pins GM [.rdi] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

/-- `GA` after a piece that changes only arrays and slots of `rSlot`. -/
theorem GA.step {p : RpP} {s t : State} (h : GA p s) {js hs : List Nat}
    (hf : Frm p.B (rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t := by
  obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
  exact ⟨I, m₀, rfl, h.step hf hjs hhs k hr, L, O, hv⟩

/-- `GA` after a piece that changes no memory. -/
theorem GA.same {p : RpP} {s t : State} (h : GA p s) (hm : t.mem = s.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t :=
  h.step (js := []) (hs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) (by simp) k hr

/-- `GA` after a piece that changes only array `j`'s first `n` bytes. -/
theorem GA.arr {p : RpP} {s t : State} (h : GA p s) {j n : Nat} (hj : j < 16) (hn : n ≤ 8 * (wk p.k + 2))
    (o : Outside p.B (slot (wk p.k) j) n s.mem t.mem) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) : GA p t :=
  h.step (Frm.rg_of_out o hn [j] [] (List.mem_singleton_self _)) (by simp [hj]) (by simp) k hr

/-! ## The head and the loads -/

theorem head_ct : RelCT isa (Two GM) (.block CrtValues.head) (Two GA) :=
  two_piece [.rdi] pins_GM (by taint_decide) fun _ s ⟨I, e, h, hv⟩ =>
    WP.mono (rpHeadS_ok h) fun _ ht => ⟨I, s.mem, e, ht, h.L, h.outs, hv⟩

theorem zeroA_ct {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two GA) (zeroA j) (Two GA) :=
  ws_ct RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) ht fun _ _ h =>
    WP.mono (zeroA_ok h.ws hj) fun _ ⟨_, o, k⟩ => h.arr hj (Nat.le_refl _) o k (by decide)

/-- `loadA`'s block and `loadBE`, from a `GA` with the pointer and the
length in the header slots `sPtr` and `sLen`. -/
theorem loadTail_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : RpP → Addr)
    (len : RpP → Nat)
    (hA : ∀ p s, GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two GA) (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) loadBE) (Two GA) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (wk p.k) j)) (ptr p) (len p)) pins_GA ht
    (fun p s h => by
      obtain ⟨hp, hl, -⟩ := hA p s h
      exact WP.mono (loadBlk_ok h.ws hP hL hp hl) fun t ⟨hbx, hsi, hcx, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hl, ⟨bs, hsrc, hbl⟩, hl1, hlw⟩ := hA p s h
      have hw := h.ws
      have hn := hw.scr.nowrap
      have sj := hw.sl hj
      have hw2 := hw.w2
      refine WP.seq (WP.mono (loadBlk_ok hw hP hL hp hl) fun t ⟨hbx, hsi, hcx, _, hm, k⟩ => ?_)
      have ht := h.same hm k (by decide)
      have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
      exact WP.mono (loadBE_ok (w := (len p + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega) rfl (by omega)
        (fun i hi => hsrc'.rd i (by omega)) (fun i hi => hsrc'.val i (by omega))
        (fun i hi => Or.inr (by have := hsrc'.out i (by omega); omega))) fun t' ⟨_, o, k'⟩ =>
          ht.arr hj (by omega) o k' (by decide)

theorem loadA_ct {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32) (ptr : RpP → Addr)
    (len : RpP → Nat)
    (hA : ∀ p s, GA p s → Bignum.X86_64.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.X86_64.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * wk p.k)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two GA) (seqs (loadA j sPtr sLen)) (Two GA) :=
  RelCT.seq (zeroA_ct hj ht₁) (loadTail_ct hj hP hL ptr len hA ht₂)

/-- The three loads. -/
theorem loads_ct : RelCT isa (Two GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) (Two GA) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * wk k := fun {k} => by unfold wk; omega
  refine ct_app (by simp [loadA]) (by simp [loadA]) (loadA_ct (by decide) (by decide) (by decide) RpP.pN RpP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide)) (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct (by decide) (by decide) (by decide) RpP.pE RpP.el (fun p s h => ?_) (by taint_decide) (by taint_decide))
    (loadA_ct (by decide) (by decide) (by decide) RpP.pD RpP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide)))
  all_goals
    obtain ⟨I, m₀, rfl, h, L, -⟩ := h
    dsimp only [RpIn.pub]
    have := L.k1
  · exact ⟨h.args.n, h.args.k, ⟨_, h.n, L.nbl⟩, by omega, k8⟩
  · exact ⟨h.args.e, h.args.el, ⟨_, h.e, L.ebl⟩, L.el1, by have := L.el2; have := @k8 I.k; omega⟩
  · exact ⟨h.args.d, h.args.dl, ⟨_, h.d, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega⟩

end VG.Proof.Rsa.X86_64
