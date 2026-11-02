module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the head, loads, products and stores

The head (`head_ct`, from `main`'s entry, `GM`), the loads of `n`, `e` and
`d` (`loadA_ct`), `Recover.prod` for a length of `e` in the header
(`prod_ct`), the changes of width (`width_ct`), the pieces that write a
header slot, and the stores of the factors and the exit (`stores_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## The head and the loads -/

/-- On entry to `main`. -/
def GM (p : RpP) (s : State) : Prop := ∃ I : RpIn, pubD I = p ∧ RpPre I s ∧ I.el ≤ 8

theorem pins_GM : Pins GM [.rdi] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

/-- The arguments and `n`, `e` and `d`, which the loads read. -/
def F1 (I : RpIn) (s : State) : Prop :=
  RpArgs s.mem I.B I.k I.el I.dl I.pP I.pQ I.pN I.pE I.pD I.sv ∧ Src s I.B I.Z I.pN I.nb ∧
    Src s I.B I.Z I.pE I.eb ∧ Src s I.B I.Z I.pD I.db

theorem arr_F1 : Arr F1 := fun I s t P ⟨ha, hn, he, hd⟩ hf hP h1 h2 => by
  have hi : InScr I.B I.Z s.mem t.mem := fun x hx => hf x fun hy => absurd hx (Nat.not_le.mpr (hP _ hy).2)
  exact ⟨ha.congr fun i hi' => hf.word_eq (fun y a b hy => by have : 256 ≤ y := (hP y hy).1; unfold rArg at hi'; omega_arith)
    (by unfold rArg at hi'; omega_arith), hn.congr hi h1 h2, he.congr hi h1 h2, hd.congr hi h1 h2⟩

theorem head_gd (p : RpP) (s : State) (h : GM p s) : WP isa (.block RecoverDet.head) s (GD nv F1 p) := by
  obtain ⟨I, rfl, h, hel⟩ := h
  have L := h.L
  have hn := h.scr.nowrap
  have hZ := L.z
  have k1 := L.k1
  have k2 := L.k2
  have ⟨bW, b26, bv, bv9⟩ := rd_bounds L.k1 L.k2 L.z
  rw [show RecoverDet.head = width false ++ ([.mov .rax (.imm (BitVec.ofInt 32 (-1))),
    .store (hdr Impl.Bignum.X86_64.Public.sMask) .rax] : List Instr) from rfl]
  refine WP.block_append_iff.mpr (WP.mono (width_ok false h.scr h.rdi L.k1 L.k2 L.z h.args.k)
    fun t₀ ⟨hw₀, hf₀, k₀⟩ => ?_)
  replace hw₀ : Ws t₀ I.B I.Z (nv I.k) := hw₀
  have h256 := hw₀.h256
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₀.mem.writeW (off I.B (8 * Impl.Bignum.X86_64.Public.sMask))
      (mask true)) (by
    xrun [State.ea, hdr, hw₀.rdi, hdrOff, hw₀.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by p1_omega),
      sx_m1]; rfl) rfl) fun t₁ ⟨m₁, k₁⟩ => ?_
  have hw₁ := hw₀.congrW m₁ (by p1_omega) (by decide) k₁ (by simp)
  have hm₁ : FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 176 ≤ y ∧ y < 184 ∨ 224 ≤ y ∧ y < 232) t₀.mem t₁.mem := by
    rw [m₁]
    refine FrmP.of_writeW _ (by p1_omega) fun y h1 h2 => ?_
    simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2
    omega_arith
  have hf₁ : FrmP I.B (fun y => 48 ≤ y ∧ y < 128 ∨ 176 ≤ y ∧ y < 184 ∨ 224 ≤ y ∧ y < 232) s.mem t₁.mem := by
    refine (FrmP.of_frm hf₀ fun r hr y h1 h2 => ?_).trans hm₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] at h1 h2 ⊢ <;> omega_arith
  have ha₁ := h.args.congr fun i hi =>
    hf₁.word_eq (fun y h1 h2 hy => by unfold rArg at hi; omega_arith) (by unfold rArg at hi; omega_arith)
  have hi₁ : InScr I.B I.Z s.mem t₁.mem := fun x hx => hf₁ x fun hy => absurd hx (by simp only at hy; omega_arith)
  have kk₁ := k₀.trans k₁
  exact ⟨I, s.mem, rfl, ⟨hw₁, ha₁.p, ha₁.q, ha₁.k, ha₁.saved, hi₁, kk₁.2.2.trans h.wr,
    (kk₁.gpr (by decide)).trans h.rsp⟩, L, h.outs, hel, ⟨true, by unfold mw; rw [m₁, word_writeW_self]⟩,
    ha₁, h.n.congrK hi₁ kk₁, h.e.congrK hi₁ kk₁, h.d.congrK hi₁ kk₁⟩

theorem head_ct : RelCT isa (Two GM) (.block RecoverDet.head) (Two (GD nv F1)) :=
  two_piece [.rdi] pins_GM (by taint_decide) head_gd

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem loadTail_ct (hF : Arr F) {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : RpP → Addr) (len : RpP → Nat)
    (hA : ∀ p s, GD w F p s → Bignum.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * w p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) loadBE) (Two (GD w F)) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (w p.k) j)) (ptr p) (len p)) pins_GD ht
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
      have ht := h.same hm k (by decide) hF
      have hsrc' := hsrc.congrK (fun x _ => by rw [hm]) k
      exact WP.mono (loadBE_ok (w := (len p + 7) / 8) ht.ws.scr hsi hcx hbx hbl hl1 (by omega_arith) rfl
        (by omega_arith) (fun i hi => hsrc'.rd i (by omega_arith)) (fun i hi => hsrc'.val i (by omega_arith))
        (fun i hi => Or.inr (by have := hsrc'.out i (by omega_arith); omega_arith))) fun t' ⟨_, o, k'⟩ =>
          ht.out o (slot_256 _ _) (by omega_arith) k' (by decide) hF

theorem loadA_ct (hF : Arr F) {j sPtr sLen : Nat} (hj : j < 16) (hP : sPtr < 32) (hL : sLen < 32)
    (ptr : RpP → Addr) (len : RpP → Nat)
    (hA : ∀ p s, GD w F p s → Bignum.word s.mem p.B (8 * sPtr) = ptr p ∧
      Bignum.word s.mem p.B (8 * sLen) = BitVec.ofNat 64 (len p) ∧
      (∃ bs, Src s p.B p.Z (ptr p) bs ∧ bs.length = len p) ∧ 1 ≤ len p ∧ len p ≤ 8 * w p.k)
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr sLen))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (loadA j sPtr sLen)) (Two (GD w F)) :=
  RelCT.seq (zeroA_ct hj hF ht₁) (loadTail_ct hF hj hP hL ptr len hA ht₂)

end

theorem loads_ct : RelCT isa (Two (GD nv F1)) (seqs (loadA Impl.Bignum.X86_64.Public.aN Impl.Bignum.X86_64.Public.sN
    Impl.Bignum.X86_64.Public.sK ++ ([zeroA 1] ++ (loadA Recover.aE Impl.Bignum.X86_64.Public.sE
    Impl.Bignum.X86_64.Public.sElen ++ loadA Recover.aD Recover.sD Recover.sDl)))) (Two (GD nv F1)) := by
  have k8 : ∀ {k : Nat}, k ≤ 8 * nv k := fun {k} => by unfold nv wk; omega_arith
  refine ct_app (by simp [loadA]) (by simp) (loadA_ct arr_F1 (by decide) (by decide) (by decide) RpP.pN RpP.k
    (fun p s h => ?_) (by taint_decide) (by taint_decide)) (ct_app (by simp) (by simp [loadA])
    (ct_one (zeroA_ct (j := 1) (by decide) arr_F1 (by taint_decide))) (ct_app (by simp [loadA]) (by simp [loadA])
    (loadA_ct arr_F1 (by decide) (by decide) (by decide) RpP.pE RpP.el (fun p s h => ?_) (by taint_decide)
      (by taint_decide))
    (loadA_ct arr_F1 (by decide) (by decide) (by decide) RpP.pD RpP.dl (fun p s h => ?_) (by taint_decide)
      (by taint_decide))))
  all_goals
    obtain ⟨I, m₀, rfl, -, L, -, -, -, ha, hn, he, hd⟩ := h
    dsimp only [pubD, fk, RpIn.pub]
    have := L.k1
  · exact ⟨ha.n, ha.k, ⟨_, hn, L.nbl⟩, by omega_arith, k8⟩
  · exact ⟨ha.e, ha.el, ⟨_, he, L.ebl⟩, L.el1, by have := L.el2; have := @k8 I.k; omega_arith⟩
  · exact ⟨ha.d, ha.dl, ⟨_, hd, L.dbl⟩, L.dl1, by have := L.dl2; have := @k8 I.k; omega_arith⟩

/-! ## `d e`-like products -/

open VG.Impl.Rsa.X86_64.Keys.Recover (aE aD aM prodInit rowHead rowNext) in
/-- `prod`'s loop, from `M = 0`, for what it changes. -/
theorem prodLoop_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w) (hz : wv s.mem B (slot w aM) (2 * (w + 2)) = 0) :
    WP isa (.seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) s fun t =>
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧
      Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .r10, .r15, .r11, .r13, .rdx, .rbp, .rcx] s t := by
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  refine WP.seq (WP.mono (prodInit_ok h hel (by omega_using [he2, hw2])) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_)
  have hs₃ := h.scr.congr k₃.2.2
  refine wp_upto (a := 0) (N := (el + 7) / 8) (by omega_using [he1]) (ProdInv s₃ B Z w)
    (fun j _ hj t hI => prodStep_ok hI (by omega_using [hw1]) (by omega_using [hw2]) hZ (by omega_using [he2]) hj h12 hbx h10 h15 h11)
    (fun t hI => ?_) ⟨hs₃, Keep.refl _ _, h13, Outside.refl _ _ _ _, by rw [m₃, hz, wv, Nat.mul_zero]⟩
  exact ⟨fun x hx => by rw [hI.out x hx, m₃], (k₃.trans hI.keep).mono (by decide)⟩

/-- `M`'s first `n` words are zero. -/
def ZM (w : Nat → Nat) (n : Nat → Nat) (I : RpIn) (s : State) : Prop :=
  wv s.mem I.B (slot (w I.k) Recover.aM) (n I.k) = 0

/-- The registers `prod`'s loop needs pinned. -/
def prodVal (w : Nat → Nat) (el : RpP → Nat) (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 (w p.k)
  | .rbx => off p.B (slot (w p.k) Recover.aE)
  | .r10 => off p.B (slot (w p.k) Recover.aM)
  | .r15 => off p.B (slot (w p.k) Recover.aD)
  | .r11 => BitVec.ofNat 64 ((el p + 7) / 8)
  | .r13 => BitVec.ofNat 64 0
  | _ => 0

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem zeroM_ct (hF : Arr F) : RelCT isa (Two (GD w F)) (zeroA Recover.aM)
    (Two (GD w fun I s => F I s ∧ ZM w (fun k => w k + 2) I s)) :=
  two_post ((zeroA_ct (by decide) hF (by taint_decide)).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h =>
    WP.mono (zeroA_ok h.ws (j := Recover.aM) (by decide)) fun t ⟨z, o, k⟩ =>
      (h.out o (slot_256 _ _) (slot_Z h (by decide)) k (by decide) hF).mono fun I e hFI => by
        subst e; exact ⟨hFI, z⟩

theorem zeroM1_ct (hF : Arr F) : RelCT isa (Two (GD w fun I s => F I s ∧ ZM w (fun k => w k + 2) I s))
    (zeroA (Recover.aM + 1)) (Two (GD w fun I s => F I s ∧ ZM w (fun k => 2 * (w k + 2)) I s)) :=
  two_post ((zeroA_ct (j := Recover.aM + 1) (F := F) (by decide) hF (by taint_decide)).mono
    (fun _ _ h => two_mono (fun _ _ h => h.mono fun _ _ h => h.1) h) fun _ _ _ => trivial) fun p s h => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI, z₁⟩ := id h
    have hw := h'.ws
    have hn := hw.scr.nowrap
    have hZ := hw.hZ
    refine WP.mono (zeroA_ok hw (j := Recover.aM + 1) (by decide)) fun t ⟨z, o, k⟩ => ?_
    have sl := hw.sl (j := Recover.aM + 1) (by decide)
    have eM1 : slot (w I.k) (Recover.aM + 1) = slot (w I.k) Recover.aM + 8 * (w I.k + 2) := by
      simp only [Bignum.slot, hdrBytes, Recover.aM]; omega_arith
    refine (h.mono (F' := F) fun _ _ h => h.1).out o (slot_256 _ _) sl k (by decide) hF |>.mono fun J e hFJ => ?_
    have eB : J.B = I.B := congrArg RpP.B e
    have eK : J.k = I.k := congrArg RpP.k e
    refine ⟨hFJ, ?_⟩
    simp only [ZM]
    rw [eB, eK, show 2 * (w I.k + 2) = (w I.k + 2) + (w I.k + 2) by omega_arith, wv_add, ← eM1, z,
      o.wv (Or.inl (by omega_arith)) (by omega_arith), z₁, Nat.mul_zero]

theorem prodLoop_ct (hF : Arr F) (el : RpP → Nat)
    (hel : ∀ p s, GD w F p s → word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (el p) ∧
      1 ≤ el p ∧ el p ≤ 8 * w p.k) :
    RelCT isa (Two (GD w fun I s => F I s ∧ ZM w (fun k => 2 * (w k + 2)) I s))
      (.seq (.block Recover.prodInit) (.loop (.seq (.block Recover.rowHead) (.seq mulAddRow
        (.block Recover.rowNext))) .ne)) (Two (GD w F)) :=
  pin_ct [.rdi] [.rdi, .r12, .rbx, .r10, .r15, .r11, .r13] (prodVal w el) pins_GD (by taint_decide)
    (fun p s h => by
      obtain ⟨e1, e2, e3⟩ := hel p s (h.mono fun _ _ h => h.1)
      have hw2 := h.ws.w2
      exact WP.mono (prodInit_ok h.ws e1 (by omega_arith)) fun t ⟨h12, hbx, h10, h15, h11, h13, hdi, _⟩ r hr => by
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
      obtain ⟨e1, e2, e3⟩ := hel p s (h.mono fun _ _ h => h.1)
      have hz : wv s.mem p.B (slot (w p.k) Recover.aM) (2 * (w p.k + 2)) = 0 := by
        obtain ⟨I, m₀, rfl, -, -, -, -, -, -, z⟩ := h; exact z
      have hw := h.ws
      have sl := hw.sl (j := Recover.aM + 1) (by decide)
      have eM1 : slot (w p.k) (Recover.aM + 1) = slot (w p.k) Recover.aM + 8 * (w p.k + 2) := by
        simp only [Bignum.slot, hdrBytes, Recover.aM]; omega_arith
      exact WP.mono (prodLoop_frm hw e1 e2 e3 hz) fun t ⟨o, k⟩ =>
        (h.mono (F' := F) fun _ _ h => h.1).out o (slot_256 _ _) (by omega_arith) k (by decide) hF

theorem prod_ct (hF : Arr F) (el : RpP → Nat)
    (hel : ∀ p s, GD w F p s → word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (el p) ∧
      1 ≤ el p ∧ el p ≤ 8 * w p.k) :
    RelCT isa (Two (GD w F)) (seqs Recover.prod) (Two (GD w F)) := by
  simp only [Recover.prod, seqs]
  exact RelCT.seq (zeroM_ct hF) (RelCT.seq (zeroM1_ct hF) (prodLoop_ct hF el hel))

/-! ## The widths and the header -/

theorem width_gd (wide : Bool) (hF : Stab F fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232) (p : RpP) (s : State)
    (h : GD w F p s) : WP isa (.block (width wide)) s (GD (fun k => widthOf wide k) F p) := by
  obtain ⟨I, m₀, rfl, h', L, O, he, ⟨c, hc⟩, hFI⟩ := h
  have h256 := h'.ws.h256
  refine WP.mono (h'.width wide L) fun t ⟨ht, _, f, k⟩ => ⟨I, m₀, rfl, ht, L, O, he, ⟨c, ?_⟩,
    hF I s t _ hFI f (fun y hy => ⟨hy, by omega_arith⟩) k.2.1 k.2.2⟩
  unfold mw at hc ⊢
  rw [f.word_eq (fun y h1 h2 hy => by simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

theorem width_ct (wide : Bool) (hF : Stab F fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (width wide)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.block (width wide)) (Two (GD (fun k => widthOf wide k) F)) :=
  two_piece [.rdi] pins_GD ht (width_gd wide hF)

/-- A block that stores `v p` to the header slot `i`, adding it to the facts. -/
theorem hdr_gd {blk : List Instr} {i : Nat} (hi : DOk (8 * i)) (hi' : i < 32)
    (hne : i ≠ Impl.Bignum.X86_64.Public.sMask) (v : RpP → BitVec 64)
    (hF : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8)
    (hok : ∀ p s, GD w F p s → WP isa (.block blk) s fun t => t.mem = s.mem.writeW (off p.B (8 * i)) (v p) ∧
      ∃ regs, Keep regs s t ∧ .rdi ∉ regs ∧ .rsp ∉ regs) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (.block blk) s (GD w (fun I t => F I t ∧ word t.mem I.B (8 * i) = v (pubD I)) p) :=
  WP.mono (hok p s h) fun t ⟨hm, regs, k, h1, h2⟩ => h.hdrW hm hi hi' k ⟨h1, h2⟩ (fun e => absurd e hne)
    fun I e hFI => by
      subst e
      exact stab_writeW hF h.ws.h256 hi' hFI hm k.2.1 k.2.2

end

/-! ## The stores and the exit -/

/-- Before the stores: the working space, the outputs' pointers and length,
and the mask. -/
def GT (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, pubD I = p ∧ Ws s I.B I.Z (nv I.k) ∧ word s.mem I.B (8 * Recover.sP) = I.pP ∧
    word s.mem I.B (8 * Recover.sQ) = I.pQ ∧
    word s.mem I.B (8 * Impl.Bignum.X86_64.Public.sK) = BitVec.ofNat 64 I.k ∧ s.wr = I.W ∧ RpLens I ∧
    RpOuts I ∧ ∃ c, mw s.mem I.B = mask c

theorem GD.gt {F : RpIn → State → Prop} {p : RpP} {s : State} (h : GD nv F p s) : GT p s := by
  obtain ⟨I, m₀, e, h, L, O, -, hm, -⟩ := h
  exact ⟨I, e, h.ws, h.p, h.q, h.k, h.wr, L, O, hm⟩

theorem pins_GT : Pins GT [.rdi] := fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [h₁.rdi, h₂.rdi]
  exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm

theorem storeA_ct {j sPtr : Nat} (hj : j < 16) (hP : sPtr < 32) (ptr : RpP → Addr)
    (hA : ∀ p s, GT p s → Bignum.word s.mem p.B (8 * sPtr) = ptr p ∧
      (∀ i < p.k, InRegions p.W (ptr p + BitVec.ofNat 64 i) 1) ∧
      (∀ i < p.k, p.Z ≤ ofs p.B (ptr p + BitVec.ofNat 64 i)))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (ws ++ base j .rbx ++ ([.mov .rsi (.mem (hdr sPtr)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK)), .mov .r15 (.mem (hdr Impl.Bignum.X86_64.Public.sMask))] :
        List Instr))) hc).isSome = true) :
    RelCT isa (Two GT) (seqs (storeA j sPtr Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask))
      (Two GT) :=
  pin_ct [.rdi] [.rdi, .rbx, .rsi, .rcx] (fun p => ioVal p.B (off p.B (slot (nv p.k) j)) (ptr p) p.k) pins_GT ht
    (fun p s h => by
      obtain ⟨hp, -⟩ := hA p s h
      obtain ⟨I, rfl, hw, -, -, hk, -⟩ := h
      exact WP.mono (storeBlk_ok hw hP (by decide) hp hk) fun t ⟨hbx, hsi, hcx, hdi⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdi
        · exact hbx
        · exact hsi
        · exact hcx)
    (by taint_decide) fun p s h => by
      obtain ⟨hp, hwr, hsep⟩ := hA p s h
      obtain ⟨I, rfl, hw, hP', hQ', hk, hW, L, O, c, hm⟩ := h
      dsimp only [pubD, fk, RpIn.pub] at hp hwr hsep ⊢
      have hn := hw.scr.nowrap
      have h256 := hw.h256
      refine WP.mono (storeA_ws hw hj hP (by decide) hp hk hm (by have := L.k1; omega_arith)
        (by have := L.k1; unfold nv wk; omega_arith) (fun i hi => by rw [hW]; exact hwr i hi) hsep)
        fun t ⟨_, _, ht, hf, k⟩ => ?_
      have fw : ∀ i < 32, Bignum.word t.mem I.B (8 * i) = Bignum.word s.mem I.B (8 * i) :=
        fun i hi => hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega_arith))
          (by omega_arith)
      exact ⟨I, rfl, ht, (fw _ (by decide)).trans hP', (fw _ (by decide)).trans hQ', (fw _ (by decide)).trans hk,
        k.2.2.trans hW, L, O, c, (fw _ (by decide)).trans hm⟩

theorem stores_ct : RelCT isa (Two GT) (seqs (storeA 10 Recover.sP Impl.Bignum.X86_64.Public.sK
    Impl.Bignum.X86_64.Public.sMask ++ (storeA 11 Recover.sQ Impl.Bignum.X86_64.Public.sK
    Impl.Bignum.X86_64.Public.sMask ++ ([.block retMask] : List (Prog isa))))) fun _ _ => True := by
  refine (ct_app (by simp [storeA]) (by simp [storeA])
    (storeA_ct (by decide) (by decide) RpP.pP (fun p s h => ?_) (by taint_decide))
    (ct_app (by simp [storeA]) (by simp)
      (storeA_ct (by decide) (by decide) RpP.pQ (fun p s h => ?_) (by taint_decide))
      (ct_one (Ψ := fun (_ : RpP) (_ : State) => True)
        ((two_taint [.rdi] pins_GT (by taint_decide)).mono (fun _ _ h => h)
          fun _ _ _ => ⟨default, trivial, trivial⟩)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  all_goals
    obtain ⟨I, rfl, -, hP', hQ', -, -, -, O, -⟩ := h
    dsimp only [pubD, fk, RpIn.pub]
  · exact ⟨hP', O.p, O.sp⟩
  · exact ⟨hQ', O.q, O.sq⟩

end VG.Proof.Rsa.X86_64.Rd
