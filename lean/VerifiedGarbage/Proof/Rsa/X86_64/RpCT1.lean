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


/-- `ws`, a block checked from `rdi`, `r12` and `r9` that leaves the
registers `rs₂` with values of the public data, and code checked from
`rs₂`. -/
theorem ws_pin_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {c₂ : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc₁).isSome = true)
    (rs₂ : List Reg) (f : α → Reg → BitVec 64)
    (hp : ∀ a s, Φ a s → WP isa (.block (ws ++ rest)) s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (ws ++ rest)) c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) c₂) (Two Ψ) := by
  refine RelCT.block_seq (RelCT.seq (two_piece (Ψ := fun a t => (∀ r ∈ [.rdi, .r12, .r9], t.gpr r = wsVal (B a) (w a) r) ∧
      WP isa (.block rest) t (fun u => ∀ r ∈ rs₂, u.gpr r = f a r) ∧ WP isa (.seq (.block rest) c₂) t (Ψ a))
      [.rdi] (fun a s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
      (by taint_decide) fun a s h => ?_)
    (pin_ct [.rdi, .r12, .r9] rs₂ f (fun a s₁ s₂ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₁
      (fun a t h => h.2.1) ht₂ fun a t h => h.2.2))
  have e₁ := WP.block_append_iff.mp (hp a s h)
  have e₂ := WP.block_seq_iff.mp (hw a s h)
  refine WP.mono (WP.and (WP.and (hws a s h).ws_ok e₁) (WP.seq_iff.mp e₂)) fun t ⟨⟨⟨h12, h9, _, k⟩, w₁⟩, w₂⟩ =>
    ⟨fun r hr => ?_, w₁, w₂⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans (hws a s h).rdi
  · exact h12
  · exact h9

namespace Rp

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

/-! ## Values between the pieces -/

/-- `GA` with facts `F` about the memory. -/
def GV (F : RpIn → Mem → Prop) (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ F I s.mem

theorem GV.ga {F : RpIn → Mem → Prop} {p : RpP} {s : State} (h : GV F p s) : GA p s := by
  obtain ⟨I, m₀, e, h, L, O, hv, -⟩ := h
  exact ⟨I, m₀, e, h, L, O, hv⟩

theorem GV.ws {F : RpIn → Mem → Prop} {p : RpP} {s : State} (h : GV F p s) : Ws s p.B p.Z (wk p.k) := h.ga.ws

theorem pins_GV {F : RpIn → Mem → Prop} : Pins (GV F) [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]

/-- `GV` after a piece, with the facts carried over. -/
theorem GV.step {F G : RpIn → Mem → Prop} {p : RpP} {s t : State} (h : GV F p s) {js hs : List Nat}
    (hf : Frm p.B (rg (wk p.k) js hs) s.mem t.mem) (hjs : ∀ j ∈ js, j < 16) (hhs : ∀ i ∈ hs, rSlot i = true)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs)
    (hFG : ∀ I : RpIn, I.pub = p → RpS I s.mem s → RpS I s.mem t → F I s.mem → G I t.mem) : GV G p t := by
  obtain ⟨I, m₀, rfl, h, L, O, hv, hF⟩ := h
  have h' := h.step hf hjs hhs k hr
  have hS : RpS I s.mem s := { h with inScr := InScr.refl _ _ _ }
  exact ⟨I, m₀, rfl, h', L, O, hv, hFG I rfl hS (hS.step hf hjs hhs k hr) hF⟩

/-- The values of `n`, `e` and `d` in their arrays. -/
def FL (I : RpIn) (m : Mem) : Prop :=
  wv m I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧ wv m I.B (slot (wk I.k) aE) (wk I.k) = I.E ∧
    wv m I.B (slot (wk I.k) aD) (wk I.k) = I.D

/-- And `-n⁻¹`. -/
def FM (I : RpIn) (m : Mem) : Prop :=
  FL I m ∧ ((word m I.B (slot (wk I.k) aN)).toNat * (word m I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0

theorem loadsV_ct : RelCT isa (Two GA) (seqs (loadA aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
    (loadA aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++ loadA aD sD sDl))) (Two (GV FL)) :=
  two_post (loads_ct.mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h, L, O, hv⟩ := h
    exact WP.mono (rpLoads_ok h L) fun t ⟨ht, _, vN, vE, vD, _⟩ => ⟨I, m₀, rfl, ht, L, O, hv, vN, vE, vD⟩

theorem minv_ct : RelCT isa (Two (GV FL)) (.block minvBlk) (Two (GV FM)) := by
  have e : minvBlk = ws ++ (base aN .r10 ++ ([.mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15] : List Instr)) := by simp only [minvBlk, List.append_assoc]
  rw [e]
  refine ws_block_ct (rest := base aN .r10 ++ ([.mov .rbx (.mem (at0 .r10))] : List Instr) ++ minv ++
      ([.store (hdr sMinv) .r15] : List Instr)) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws)
    (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨I, m₀, eI, h', L, O, hv, vN, vE, vD⟩ := id h
  subst eI
  have hw := h'.ws
  have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
  have hodd := (valid_lo hv).1
  have hw0 : (word s.mem I.B (slot (wk I.k) aN)).toNat % 2 = 1 := by
    rw [show (word s.mem I.B (slot (wk I.k) aN)).toNat % 2 = wv s.mem I.B (slot (wk I.k) aN) (wk I.k) % 2 by
      rw [wv_low (by have := hw.w1; omega)]; omega, vN]; exact hodd
  refine WP.mono (minvBlk_ok hw hw0) fun t ⟨hi, f, k⟩ => ⟨I, m₀, rfl, h'.step f (by simp) (by decide) k (by decide),
    L, O, hv, ⟨?_, ?_, ?_⟩, hi⟩
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vN
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vE
  · rw [f.rg_wv hZ16 (by decide) (by decide) (by simp) (by omega)]; exact vD

/-! ## `M = d e` and its check -/

def FZ1 (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (wk I.k + 2) = 0
def FZ2 (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = 0
def FP (I : RpIn) (m : Mem) : Prop := FM I m ∧ wv m I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = I.D * I.E

theorem zeroAV_ct {F : RpIn → Mem → Prop} {j : Nat} (hj : j < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two (GV F)) (zeroA j) fun _ _ => True :=
  (zeroA_ct hj ht).mono (fun _ _ h => two_mono (Φ := GV F) (fun _ _ h => GV.ga h) h) fun _ _ _ => trivial

theorem zeroM_ct : RelCT isa (Two (GV FM)) (zeroA aM) (Two (GV FZ1)) :=
  two_post (zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨vN, vE, vD⟩, hi⟩ := id h
    have hw := h'.ws
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM) (by decide)) fun t ⟨z, o, k⟩ => ?_
    have f : Frm I.B (rg (wk I.k) [aM] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, z⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi

theorem zeroM1_ct : RelCT isa (Two (GV FZ1)) (zeroA (aM + 1)) (Two (GV FZ2)) :=
  two_post (zeroAV_ct (by decide) (by taint_decide)) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, z₁⟩ := id h
    have hw := h'.ws
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
    refine WP.mono (zeroA_ok hw (j := aM + 1) (by decide)) fun t ⟨z, o, k⟩ => ?_
    have f : Frm I.B (rg (wk I.k) [aM + 1] []) s.mem t.mem := Frm.rg_of_out o (Nat.le_refl _) _ _ (by decide)
    have eM1 : slot (wk I.k) (aM + 1) = slot (wk I.k) aM + 8 * (wk I.k + 2) := by simp only [slot, hdrBytes, aM]; omega
    refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
    · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
    · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
    · rw [show 2 * (wk I.k + 2) = (wk I.k + 2) + (wk I.k + 2) by omega, wv_add, ← eM1, z,
        f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega), z₁, Nat.mul_zero]

/-- The registers `prod`'s loop needs pinned. -/
def prodVal (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 (wk p.k)
  | .rbx => off p.B (slot (wk p.k) aE)
  | .r10 => off p.B (slot (wk p.k) aM)
  | .r15 => off p.B (slot (wk p.k) aD)
  | .r11 => BitVec.ofNat 64 ((p.el + 7) / 8)
  | .r13 => BitVec.ofNat 64 0
  | _ => 0

theorem prodLoop_ct : RelCT isa (Two (GV FZ2))
    (.seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) (Two (GV FP)) :=
  pin_ct [.rdi] [.rdi, .r12, .rbx, .r10, .r15, .r11, .r13] prodVal pins_GV (by taint_decide)
    (fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, -⟩ := id h
      exact WP.mono (prodInit_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
        fun t ⟨h12, hbx, h10, h15, h11, h13, hdi, _⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hdi
          · exact h12
          · exact hbx
          · exact h10
          · exact h15
          · exact h11
          · exact h13)
    (by taint_decide) fun p s h => by
      obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, hz⟩ := id h
      have hw := h'.ws
      have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega
      have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
        have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
      have sM := hw.sl (j := aM + 1) (by decide)
      refine WP.mono (prodLoop_ok hw h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
        (by rw [vE]; exact hEl) hz) fun t ⟨vM, o, k⟩ => ?_
      have f : Frm I.B (rg (wk I.k) [aM, aM + 1] []) s.mem t.mem :=
        Frm.rg_of_out2 o (Nat.le_refl _) _ _ (by decide) (by decide)
      refine ⟨I, m₀, rfl, h'.step f (by decide) (by simp) k (by decide), L, O, hv, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩⟩
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vN
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vE
      · rw [f.rg_wv hZ16 (by simp) (by decide) (by decide) (by omega)]; exact vD
      · rw [f.rg_word0 hZ16 (by simp) (by decide) (by decide), f.rg_word (by decide) (by simp)]; exact hi
      · rw [vM, vD, vE]

theorem prod_ct : RelCT isa (Two (GV FM)) (seqs prod) (Two (GV FP)) := by
  simp only [prod, seqs]
  exact RelCT.seq zeroM_ct (RelCT.seq zeroM1_ct prodLoop_ct)

/-- The registers the check of `M` needs pinned. -/
def skipVal (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .rbx => off p.B (slot (wk p.k) aM)
  | .r12 => BitVec.ofNat 64 (wk p.k + (p.el + 7) / 8)
  | _ => 0

theorem skipBlk_eq : skipBlk = ws ++ (base aM .rbx ++
    ([.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .rax), .alu .and .rdx (.imm 1), .alu .sub .rax (.reg .rdx),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sElen)), .alu .add .rcx (.imm 7), .shift .shr .rcx 3,
      .alu .add .rcx (.mem (hdr sW)), .mov .r12 (.reg .rcx), .store (at0 .rbx) .rax, .alu .sub .rdx (.imm 1),
      .store (hdr sC2) .rdx, .mov32 .rbp (.imm 0)] : List Instr)) := by
  simp only [skipBlk, List.append_assoc]

theorem skip_ct : RelCT isa (Two (GV FP)) (seqs [.block skipBlk, wordLoop 0 orBody, .block skipTest])
    fun _ _ => True := by
  simp only [seqs]
  rw [skipBlk_eq]
  refine (ws_pin_ct (Ψ := fun _ _ => True) RpP.B RpP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide)
    [.rdi, .rbx, .r12, .rbp] skipVal (fun p s h => ?_) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · rw [← skipBlk_eq]
    obtain ⟨I, m₀, rfl, h', L, O, -⟩ := id h
    exact WP.mono (skipBlk_ok h'.ws h'.args.el (by have := L.el2; have := L.k2; omega))
      fun t ⟨hbx, hbp, h12, hdi, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact h12
        · exact hbp
  · rw [← skipBlk_eq]
    obtain ⟨I, m₀, rfl, h', L, O, hv, ⟨⟨vN, vE, vD⟩, hi⟩, vM⟩ := id h
    have hEl : I.E < 2 ^ (64 * ((I.el + 7) / 8)) := by
      have := os2ip_lt I.eb; rw [L.ebl] at this; exact Nat.lt_of_lt_of_le this (pow256_le_wk I.el)
    have hDl : I.D < 2 ^ (64 * wk I.k) := by
      have := os2ip_lt I.db; rw [L.dbl] at this
      exact Nat.lt_of_lt_of_le this (by
        rw [pow256_eq]; exact Nat.pow_le_pow_right (by decide) (by have := L.dl2; unfold wk; omega))
    have := skip_ok h'.ws h'.args.el L.el1 (by have := L.el2; unfold wk; omega)
      (by rw [vM, Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' hDl hEl)
    simp only [seqs] at this
    exact WP.mono this fun _ _ => trivial

/-- The prefix of `main` leaks the same in two runs with the same public
data. -/
theorem prefix_ct : RelCT isa (Two GM) (seqs prefixList) (Two fun (_ : RpP) (_ : State) => True) := by
  simp only [prefixList]
  refine ct_app ?_ ?_ (ct_one head_ct) (ct_app ?_ ?_ loadsV_ct (ct_app ?_ ?_ (ct_one minv_ct)
    (ct_app ?_ ?_ prod_ct (skip_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨default, trivial, trivial⟩))))
  all_goals simp [loadA, prod]

end Rp

end VG.Proof.Rsa.X86_64
