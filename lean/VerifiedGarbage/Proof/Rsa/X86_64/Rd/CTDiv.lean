module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes

/-! ### `Rsa.X86_64.Rd.CTParts`, which this module and modules that import it used -/

section

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
  refine wp_upto (a := 0) (N := (el + 7) / 8) (by omega_using [he1]) (ProdInv s₃ B Z w w)
    (fun j _ hj t hI => prodStep_ok hI (by omega_using [hw1]) (Nat.le_refl _) (by omega_using [hw2]) hZ (by omega_using [he2]) hj h12 hbx h10 h15 h11)
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

end

end

/-! ### `Rsa.X86_64.Rd.CTWords`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the word-level pieces

The stages of shifts by words and bits, their tests and selects, and the
copies through a temporary, each from `GD` (`CTBase`). A stage's branch is
on the width alone; its pieces keep the stage's mask `sB2` a mask (`MB`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Lists of pieces -/

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem ct_post {α : Type} {P : State → State → Prop} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa P c (Two Φ)) (hΦ : ∀ a s, Φ a s → Ψ a s) : RelCT isa P c (Two Ψ) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono hΦ h

theorem ct_pre {α : Type} {Q : State → State → Prop} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two Ψ) c Q) (hΦ : ∀ a s, Φ a s → Ψ a s) : RelCT isa (Two Φ) c Q :=
  h.mono (fun _ _ h => two_mono hΦ h) fun _ _ h => h

theorem ct_map {α : Type} {Φ : α → State → Prop} (f : Nat → Prog isa) :
    ∀ (l : List Nat), l ≠ [] → (∀ c ∈ l, RelCT isa (Two Φ) (f c) (Two Φ)) →
      RelCT isa (Two Φ) (seqs (l.map f)) (Two Φ)
  | [], h, _ => absurd rfl h
  | [c], _, h => ct_one (h c (by simp))
  | c :: d :: l, _, h => ct_cons (List.cons_ne_nil _ _) (h c (by simp))
      (ct_map f (d :: l) (List.cons_ne_nil _ _) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem ct_flat {α : Type} {Φ : α → State → Prop} (g : Nat → List (Prog isa)) (hg : ∀ c, g c ≠ []) :
    ∀ (l : List Nat), l ≠ [] → (∀ c ∈ l, RelCT isa (Two Φ) (seqs (g c)) (Two Φ)) →
      RelCT isa (Two Φ) (seqs (l.map g).flatten) (Two Φ)
  | [], h, _ => absurd rfl h
  | [c], _, h => by simpa using h c (by simp)
  | c :: d :: l, _, h => by
      rw [List.map_cons, List.flatten_cons]
      exact ct_app (hg c) (by simp [hg d]) (h c (by simp))
        (ct_flat g hg (d :: l) (List.cons_ne_nil _ _) fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Facts of the header -/

/-- The stage's `keep` a mask. -/
def MB (I : RpIn) (s : State) : Prop := ∃ b, word s.mem I.B (8 * sB2) = mask b

theorem stab_MB {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 216 ∨ 224 ≤ y) : Stab MB Q :=
  fun I s t P ⟨b, hb⟩ hf hP h1 h2 => ⟨b, stab_hdr (i := sB2) (by decide) (fun _ => mask b)
    (fun y hy => by have := hQ y hy; simp only [sB2, sFn]; omega_arith) I s t P hb hf hP h1 h2⟩

theorem stab_const (P : RpIn → Prop) {Q : Nat → Prop} : Stab (fun I _ => P I) Q :=
  fun _ _ _ _ h _ _ _ _ => h

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- `GD` after `sB2 := mask b`. -/
theorem GD.setB {p : RpP} {s t : State} (h : GD w F p s) {b : Bool}
    (hm : t.mem = s.mem.writeW (off p.B (8 * sB2)) (mask b)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) :
    GD w (fun I s => F I s ∧ MB I s) p t :=
  h.hdrW hm (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k hr (fun e => absurd e (by decide))
    fun I e hFI => by
      have eB : p.B = I.B := (congrArg RpP.B e).symm
      have eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
      have hZ := h.ws.h256
      rw [eB] at hm
      rw [eZ] at hZ
      obtain ⟨a, b'⟩ := stab_writeW hF hZ (by decide) hFI hm k.2.1 k.2.2
      exact ⟨a, _, b'⟩

theorem GD.mb {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w (fun I s => G I s ∧ MB I s) p s) :
    ∃ b, word s.mem p.B (8 * sB2) = mask b := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, -, hb⟩ := h
  exact hb

theorem GD.fact {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w G p s) :
    ∃ I, pubD I = p ∧ G I s := by
  obtain ⟨I, m₀, e, -, -, -, -, -, hG⟩ := h
  exact ⟨I, e, hG⟩

/-- A stage: the header's compare, then a branch on the width. -/
theorem stage_ct {rest : List Instr} {th el : Prog isa} {Ψ : RpP → State → Prop} (cnd : RpP → Bool) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hhd : ∀ p s, GD w F p s → WP isa (.block (ws ++ rest)) s fun t => isa.eval .b t = some (cnd p) ∧
      t.mem = s.mem ∧ ∃ regs, Keep regs s t ∧ .rdi ∉ regs ∧ .rsp ∉ regs)
    (hth : RelCT isa (Two fun p s => GD w F p s ∧ cnd p = true) th (Two Ψ))
    (hel : RelCT isa (Two fun p s => GD w F p s ∧ cnd p = false) el (Two Ψ)) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ rest)) (.ite .b th el)) (Two Ψ) := by
  refine RelCT.seq (R := Two fun p t => GD w F p t ∧ isa.eval .b t = some (cnd p))
    (wsG_block_ct (F := F) (w := w) (fun _ _ h => h) ht fun p s h =>
      WP.mono (hhd p s h) fun t ⟨e, hm, regs, k, h1, h2⟩ => ⟨h.same hm k ⟨h1, h2⟩ hF, e⟩)
    (two_ite (fun p s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) (ct_pre hth ?_) (ct_pre hel ?_))
  · intro p s ⟨⟨h, e⟩, e'⟩
    exact ⟨h, Option.some.inj (e.symm.trans e')⟩
  · intro p s ⟨⟨h, e⟩, e'⟩
    exact ⟨h, Option.some.inj (e.symm.trans e')⟩

/-- A copy of `n` words through `rsi` to `rbx`, both within the arrays. -/
theorem copyP_gd {blk : List Instr} (hF : Arr F) (n od os : RpP → Nat)
    (hblk : ∀ p s, GD w F p s → WP isa (.block blk) s fun u => u.gpr .r12 = BitVec.ofNat 64 (n p) ∧
      u.gpr .rsi = off p.B (os p) ∧ u.gpr .rbx = off p.B (od p) ∧ u.mem = s.mem ∧
      Keep [.r12, .r9, .rsi, .rbx] s u)
    (hb : ∀ p s, GD w F p s → 1 ≤ n p ∧ 256 ≤ od p ∧ od p + 8 * n p ≤ slot (w p.k) 16 ∧ 256 ≤ os p ∧
      os p + 8 * n p ≤ slot (w p.k) 16 ∧ (os p + 8 * n p ≤ od p ∨ od p + 8 * n p ≤ os p))
    (p : RpP) (s : State) (h : GD w F p s) : WP isa (.seq (.block blk) copyWords) s (GD w F p) := by
  obtain ⟨n1, d1, d2, s1, s2, sep⟩ := hb p s h
  have hw := h.ws
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  have e16 := slotE (w p.k) 16
  refine WP.seq (WP.mono (hblk p s h) fun u ⟨h12, hsi, hbx, m, k⟩ => ?_)
  have hs := hw.scr.congr k.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 n1 (by omega_arith) (by omega_arith)
    (fun i hi => hs.ld (by omega_arith)) (fun i hi => hs.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off p.B (by omega_arith)]; omega_arith)) fun t ⟨_, _, o, k'⟩ => ?_
  rw [m] at o
  exact h.out o d1 (by omega_arith) (k.trans k') (by decide) hF

theorem copyP_ct {rest : List Instr} (hF : Arr F) (n od os : RpP → Nat)
    (hblk : ∀ p s, GD w F p s → WP isa (.block (ws ++ rest)) s fun u => u.gpr .r12 = BitVec.ofNat 64 (n p) ∧
      u.gpr .rsi = off p.B (os p) ∧ u.gpr .rbx = off p.B (od p) ∧ u.mem = s.mem ∧
      Keep [.r12, .r9, .rsi, .rbx] s u)
    (hb : ∀ p s, GD w F p s → 1 ≤ n p ∧ 256 ≤ od p ∧ od p + 8 * n p ≤ slot (w p.k) 16 ∧ 256 ≤ os p ∧
      os p + 8 * n p ≤ slot (w p.k) 16 ∧ (os p + 8 * n p ≤ od p ∨ od p + 8 * n p ≤ os p))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) copyWords) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ rest)) copyWords) (Two (GD w F)) :=
  wsG_ct (fun _ _ h => h) ht (copyP_gd hF n od os hblk hb)

/-- `selK wd j t`, for `sB2` a mask. -/
theorem selK_eq (wd : Bool) (j t : Nat) : selK wd j t = .seq (.block (ws ++ ((if wd then wideR else []) ++
    (base j .r8 ++ (base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr)))))) (wordLoop 0 selBody) := by
  simp only [selK, wsW, List.append_assoc]

theorem selK_ct (wd : Bool) {j t : Nat} (hj : j + (if wd then 2 else 1) ≤ 16) (ht' : t + (if wd then 2 else 1) ≤ 16)
    (hjt : ∀ w, slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j) (hF : Arr F)
    (hb : ∀ p s, GD w F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if wd then wideR else []) ++
      (base j .r8 ++ (base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr))))) (wordLoop 0 selBody))
      hc).isSome = true) :
    RelCT isa (Two (GD w F)) (selK wd j t) (Two (GD w F)) := by
  rw [selK_eq]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    have e : ws ++ ((if wd then wideR else []) ++ (base j .r8 ++ (base t .rsi ++
        ([.mov .rbp (.mem (hdr sB2))] : List Instr)))) = ws ++ (if wd then wideR else []) ++ base j .r8 ++
        base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr) := by simp only [List.append_assoc]
    rw [e]
    exact sel_gd (fun _ _ h => h) wd hj ht' hjt hF (fun p s h => by
      obtain ⟨b, hb⟩ := hb p s h
      exact ⟨b, maskLd (by decide) h.ws.h256 hb⟩) p s h

end

/-! ## Shifts by bits, for what they change -/

theorem shrClF_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j t c : Nat} {pre : List Instr}
    (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hc : c < 64) (hpre : ClPre B Z s.mem pre c) :
    WP isa (shrCl false j t pre) s fun u =>
      Outside B (slot w t) (8 * w) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rcx, .rax, .rdx, .r14] s u := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have st := h.sl ht
  have pj := slot_far (w := w) hjt
  have hw1 := h.w1
  have hw2 := h.w2
  unfold shrCl
  refine WP.seq (WP.mono (clBlk_ok h false hpre) fun s₁ ⟨h12, h8, hsi, hcx, m₁, k₁⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at h12
  refine WP.mono (shrCl_ok hc (h.scr.congr k₁.2.2) hsi h8 h12 hcx (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨_, o, k₂⟩ => ?_
  rw [m₁] at o
  exact ⟨o, (k₁.trans k₂).mono (by simp)⟩

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem shrCl_ct {j t : Nat} {pre : List Instr} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem pre c) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ (base t .rsi ++ pre)))
      (wordLoop 0 shrClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (shrCl false j t pre) (Two (GD w F)) := by
  have e : shrCl false j t pre = .seq (.block (ws ++ (base j .r8 ++ (base t .rsi ++ pre)))) (wordLoop 0 shrClBody) := by
    simp only [shrCl, wsW, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    obtain ⟨c, hc, hp⟩ := hpre p s h
    exact WP.mono (shrClF_ok h.ws hj ht' hjt hc hp) fun _ ⟨o, k⟩ =>
      h.out o (slot_256 _ _) (by have := slot_Z h ht'; omega_arith) k (by decide) hF

theorem shlCl_ct (wd : Bool) {j t : Nat} {pre : List Instr} (hj : j + (if wd then 2 else 1) ≤ 16)
    (ht' : t + (if wd then 2 else 1) ≤ 16)
    (hjt : ∀ w, slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j) (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem pre c) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if wd then wideR else []) ++
      (base j .r8 ++ (base t .rsi ++ (pre ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] :
        List Instr)))))) (wordLoop 1 shlClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (shlCl wd j t pre) (Two (GD w F)) := by
  have e : shlCl wd j t pre = .seq (.block (ws ++ ((if wd then wideR else []) ++ (base j .r8 ++ (base t .rsi ++
      (pre ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] : List Instr)))))))
      (wordLoop 1 shlClBody) := by
    simp only [shlCl, wsW, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    obtain ⟨c, hc, hp⟩ := hpre p s h
    refine WP.mono (shlClP_ok h.ws wd hj ht' (hjt _) hc hp) fun _ ⟨_, o, k⟩ =>
      h.out o (slot_256 _ _) ?_ k (by decide) hF
    have r1 := slot_room (w := w p.k) ht'
    have r2 := h.ws.hZ
    cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at r1 ⊢ <;> omega_arith

theorem testW_ct (both : Bool) {c : Nat} (hc1 : 1 ≤ c) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hw : ∀ p s, GD w F p s → c ≤ w p.k) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 (if both then or2Body else or1Body)) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (testW both c)) (Two (GD w fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testW both c) = .seq (.seq (.block (ws ++ (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))))
      (wordLoop 0 (if both then or2Body else or1Body))) (.block keepOf) := by
    simp only [testW, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testW_ok h.ws both hc1 (hw p s h)) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

theorem testB_ct (both : Bool) {b : Nat} (hb1 : 1 ≤ b) (hb32 : b ≤ 32)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (testB both b)) (Two (GD w fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testB both b) = .block (ws ++ (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) := by
    simp only [testB, seqs, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    exact WP.mono (testB_ok h.ws both hb1 hb32) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

theorem shrWords_ct {j c t : Nat} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hc64 : c ≤ 64) (hF : Arr F)
    (hw : ∀ p s, GD w F p s → c + 1 ≤ w p.k) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base j .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx))))
      copyWords) hc₂).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shrWords j c t)) (Two (GD w F)) := by
  have e : shrWords j c t = [zeroA t, .seq (.block (ws ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base j .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx)))))
      copyWords] := by
    simp only [shrWords, List.append_assoc]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct ht' hF ht₁) (ct_one (copyP_ct hF (fun p => w p.k - c)
    (fun p => slot (w p.k) t) (fun p => slot (w p.k) j + 8 * c) (fun p s h => ?_) (fun p s h => ?_) ht₂))
  · have e' : ws ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++
        (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx))) =
        ws ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx := by
      simp only [List.append_assoc]
    rw [e']
    exact shrWB_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) (j := j) (c := 1) (by omega_arith)
    have r2 := slot_room (w := w p.k) (j := t) (c := 1) (by omega_arith)
    have sep := slot_far (w := w p.k) hjt
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

theorem shlWordsT_ct {j c t : Nat} (hj : j + 2 ≤ 16) (ht' : t + 2 ≤ 16) (hjt : j + 2 ≤ t ∨ t + 2 ≤ j)
    (hc64 : c ≤ 64) (hF : Arr F) (hw : ∀ p s, GD w F p s → c + 2 ≤ w p.k) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base (t + 1) .r8)) zeroAccLoop)
      hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) hc₃).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shlWords true j c t)) (Two (GD w F)) := by
  have e : shlWords true j c t = [zeroA t, zeroA (t + 1), .seq (.block (ws ++ (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))))) copyWords] := by
    simp only [shlWords, wsW, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct (by omega_arith) hF ht₁)
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (by omega_arith) hF ht₂) (ct_one (copyP_ct hF
    (fun p => 2 * w p.k + 2 - c) (fun p => slot (w p.k) t + 8 * c) (fun p => slot (w p.k) j)
    (fun p s h => ?_) (fun p s h => ?_) ht₃)))
  · have e' : ws ++ (wideR ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++
        (base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))) =
        wsW true ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) := by
      simp only [wsW, ↓reduceIte, List.append_assoc]
    rw [e']
    exact shlWB_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) hj
    have r2 := slot_room (w := w p.k) ht'
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    have sep : slot (w p.k) j + 2 * (8 * (w p.k + 2)) ≤ slot (w p.k) t ∨
        slot (w p.k) t + 2 * (8 * (w p.k + 2)) ≤ slot (w p.k) j := by
      rcases hjt with h' | h'
      · left; have := slot_mono (w := w p.k) h'; rw [slot_add] at this; omega_arith
      · right; have := slot_mono (w := w p.k) h'; rw [slot_add] at this; omega_arith
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

end

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.wkf {G : RpIn → State → Prop} {P : Nat → Prop} {p : RpP} {s : State} (h : GD w G p s)
    (hG : ∀ I s, G I s → P (w I.k)) : P (w p.k) := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h
  exact hG I s hI

theorem GD.kIn {G : RpIn → State → Prop} {P : Nat → Prop} {p : RpP} {s : State} (h : GD w G p s)
    (hp : P (w p.k)) : GD w (fun I s => G I s ∧ P (w I.k)) p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hI⟩ := h
  exact ⟨I, m₀, rfl, h', L, O, he, hm, hI, hp⟩

theorem arr_k (hF : Arr F) (P : Nat → Prop) : Arr fun I s => F I s ∧ P (w I.k) :=
  hF.and (stab_const _)

theorem arr_mb {G : RpIn → State → Prop} (hG : Arr G) : Arr fun I s => G I s ∧ MB I s :=
  hG.and (stab_MB fun y hy => .inr (by omega_arith))

theorem sel_far (j t : Nat) (hjt : j ≠ t) : ∀ w, slot w j + 8 * shlN false w ≤ slot w t ∨
    slot w t + 8 * shlN false w ≤ slot w j := fun w => by
  have := slot_far (w := w) hjt
  simp only [shlN, Bool.false_eq_true, ↓reduceIte]
  omega_arith

theorem sel_4_14 : ∀ w, slot w 4 + 8 * shlN true w ≤ slot w 14 ∨ slot w 14 + 8 * shlN true w ≤ slot w 4 :=
  fun w => by
    simp only [shlN, ↓reduceIte, slotE]
    omega_arith

/-- A stage of `c` words of the twos. -/
theorem stageW_ct (both : Bool) {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 2)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 (if both then or2Body else or1Body)) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base 7 .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base 14 .rbx))))
      copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base 6 .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base 14 .rbx))))
      copyWords) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 4 .rsi ++ (base 14 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₄).isSome = true) :
    RelCT isa (Two (GD w F)) (stageW both c) (Two (GD w F)) := by
  unfold stageW
  refine stage_ct (cnd := fun p => decide (w p.k < c + 2)) hF t₀ (fun p s h => WP.mono (stageHd_ok h.ws hc64)
    fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG := arr_k (w := w) hF (fun x => c + 2 ≤ x)
  have hGB := arr_mb hG
  have hGb : Stab (fun I s => F I s ∧ c + 2 ≤ w I.k) fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8 :=
    hFb.and (stab_const _)
  refine ct_pre (Ψ := GD w fun I s => F I s ∧ c + 2 ≤ w I.k) ?_ fun p s ⟨h, hc⟩ =>
    h.kIn (P := fun x => c + 2 ≤ x) (by simp only [decide_eq_false_iff_not] at hc; omega_arith)
  have hw1 : ∀ p s, GD w (fun I s => (F I s ∧ c + 2 ≤ w I.k) ∧ MB I s) p s → c + 1 ≤ w p.k := fun p s h =>
    h.wkf (P := fun x => c + 1 ≤ x) fun I s hI => by have := hI.1.2; omega_arith
  have hw2 : ∀ p s, GD w (fun I s => (F I s ∧ c + 2 ≤ w I.k) ∧ MB I s) p s → c + 2 ≤ w p.k := fun p s h =>
    h.wkf (P := fun x => c + 2 ≤ x) fun I s hI => hI.1.2
  have hT := testW_ct (w := w) both hc1 hGb (fun p s h => h.wkf (P := fun x => c ≤ x) fun I s hI => by
    have := hI.2; omega_arith) t₁
  have hS7 := shrWords_ct (j := 7) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw1
    (by taint_decide) t₂
  have hK7 := selK_ct (w := w) false (j := 7) (t := 14) (by decide) (by decide) (sel_far 7 14 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ct_post (ct_app (by simp [testW]) (List.cons_ne_nil _ _)
      (ct_app (by simp [testW]) (by simp [shrWords]) hT hS7) (ct_one hK7)) fun p s h => h.mono fun I _ hI => hI.1.1
  · simp only [↓reduceIte]
    have hS6 := shrWords_ct (j := 6) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw1
      (by taint_decide) t₃
    have hK6 := selK_ct (w := w) false (j := 6) (t := 14) (by decide) (by decide) (sel_far 6 14 (by decide)) hGB
      (fun _ _ h => h.mb) (by taint_decide)
    have hL4 := shlWordsT_ct (j := 4) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw2
      (by taint_decide) (by taint_decide) t₄
    have hK4 := selK_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB
      (fun _ _ h => h.mb) (by taint_decide)
    exact ct_post (ct_app (by simp [testW]) (by simp [shrWords])
      (ct_app (by simp [testW]) (List.cons_ne_nil _ _)
        (ct_app (by simp [testW]) (by simp [shrWords]) hT hS7) (ct_one hK7))
      (ct_app (by simp [shrWords]) (by simp)
        (ct_app (by simp [shrWords]) (List.cons_ne_nil _ _)
          (ct_app (by simp [shrWords]) (by simp) hS6 (ct_one hK6)) hL4) (ct_one hK4)))
      fun p s h => h.mono fun I _ hI => hI.1.1

end

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- A stage of `b` bits of the twos. -/
theorem stageB_ct (both : Bool) {b : Nat} (hb1 : 1 ≤ b) (hb32 : b ≤ 32) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .r8 ++ (base 14 .rsi ++ clOf b)))
      (wordLoop 0 shrClBody)) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 6 .r8 ++ (base 14 .rsi ++ clOf b)))
      (wordLoop 0 shrClBody)) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if true then wideR else []) ++
      (base 4 .r8 ++ (base 14 .rsi ++ (clOf b ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] :
        List Instr)))))) (wordLoop 1 shlClBody)) h₄).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (stageB both b)) (Two (GD w F)) := by
  have hGB := arr_mb hF
  have hpre : ∀ p s, GD w (fun I s => F I s ∧ MB I s) p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem (clOf b) c :=
    fun _ _ _ => ⟨b, by omega_arith, clOf_pre (by omega_arith)⟩
  have hT := testB_ct (w := w) both hb1 hb32 hFb t₁
  have hS7 := shrCl_ct (w := w) (j := 7) (t := 14) (by decide) (by decide) (by decide) hGB hpre t₂
  have hK7 := selK_ct (w := w) false (j := 7) (t := 14) (by decide) (by decide) (sel_far 7 14 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  unfold stageB
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ct_post (ct_app (by simp [testB]) (List.cons_ne_nil _ _) hT (ct_cons (List.cons_ne_nil _ _) hS7 (ct_one hK7)))
      fun p s h => h.mono fun I _ hI => hI.1
  · simp only [↓reduceIte]
    have hS6 := shrCl_ct (w := w) (j := 6) (t := 14) (by decide) (by decide) (by decide) hGB hpre t₃
    have hK6 := selK_ct (w := w) false (j := 6) (t := 14) (by decide) (by decide) (sel_far 6 14 (by decide)) hGB
      (fun _ _ h => h.mb) (by taint_decide)
    have hL4 := shlCl_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB hpre t₄
    have hK4 := selK_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB
      (fun _ _ h => h.mb) (by taint_decide)
    exact ct_post (ct_app (by simp [testB]) (List.cons_ne_nil _ _)
      (ct_app (by simp [testB]) (List.cons_ne_nil _ _) hT (ct_cons (List.cons_ne_nil _ _) hS7 (ct_one hK7)))
      (ct_cons (List.cons_ne_nil _ _) hS6 (ct_cons (List.cons_ne_nil _ _) hK6
        (ct_cons (List.cons_ne_nil _ _) hL4 (ct_one hK4)))))
      fun p s h => h.mono fun I _ hI => hI.1

end

/-- The twos' stages, at the narrow width. -/
theorem twos_ct {F : RpIn → State → Prop} (hF : Arr F) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) :
    RelCT isa (Two (GD nv F)) (seqs twos) (Two (GD nv F)) := by
  have hg : ∀ (both : Bool) (c : Nat), stageB both c ≠ [] := fun _ _ => by simp [stageB, testB]
  have hW : ∀ both : Bool, ∀ c ∈ wordStages, RelCT isa (Two (GD nv F)) (stageW both c) (Two (GD nv F)) := by
    intro both c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases both <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageW_ct _ (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide) (by taint_decide)
  have hB : ∀ both : Bool, ∀ c ∈ bitStages, RelCT isa (Two (GD nv F)) (seqs (stageB both c)) (Two (GD nv F)) := by
    intro both c hc
    simp only [bitStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases both <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageB_ct _ (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  unfold twos
  exact ct_app (by simp [wordStages, bitStages, stageB, testB]) (by simp [bitStages, stageB, testB])
    (ct_app (by simp [wordStages, bitStages, stageB, testB]) (by simp [wordStages])
      (ct_app (by simp [wordStages]) (by simp [bitStages, stageB, testB])
        (ct_map _ wordStages (by simp [wordStages]) (hW true))
        (ct_flat _ (hg true) bitStages (by simp [bitStages]) (hB true)))
      (ct_map _ wordStages (by simp [wordStages]) (hW false)))
    (ct_flat _ (hg false) bitStages (by simp [bitStages]) (hB false))

end VG.Proof.Rsa.X86_64.Rd

end

end

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the divisions' pieces

The leading zeros (`clzTop`) into `sC`, below 64 (`MC`); the shifts by them;
`divB`'s normalization by stages, which ends with the divisor's top bit set
(`FD`); `b²` by rows of `v` words. All at the wide width `W = 2 h + 4`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

theorem wW_eq (k : Nat) : wW k = 2 * wk k + 4 := by simp only [wW, nv]; omega_arith

/-- `sC`, below 64. -/
def MC (I : RpIn) (s : State) : Prop := ∃ z, z < 64 ∧ word s.mem I.B (8 * sC) = BitVec.ofNat 64 z

theorem stab_MC {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 240 ∨ 248 ≤ y) : Stab MC Q :=
  fun I s t P ⟨z, hz, e⟩ hf hP h1 h2 => ⟨z, hz, stab_hdr (i := sC) (by decide) (fun _ => BitVec.ofNat 64 z)
    (fun y hy => by have := hQ y hy; simp only [sC, sFn]; omega_arith) I s t P e hf hP h1 h2⟩

theorem arr_mc {G : RpIn → State → Prop} (hG : Arr G) : Arr fun I s => G I s ∧ MC I s :=
  hG.and (stab_MC fun y hy => .inr (by omega_arith))

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.kb {p : RpP} {s : State} (h : GD w F p s) : 8 ≤ wk p.k ∧ wk p.k ≤ 128 := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  have := L.k1
  have := L.k2
  show 8 ≤ wk I.k ∧ wk I.k ≤ 128
  unfold wk; omega_arith

/-- `GD` after `sC := z`, `z < 64`. -/
theorem GD.setC {p : RpP} {s t : State} (h : GD w F p s) {z : Nat} (hz : z < 64)
    (hm : t.mem = s.mem.writeW (off p.B (8 * sC)) (BitVec.ofNat 64 z)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    GD w (fun I s => F I s ∧ MC I s) p t :=
  h.hdrW hm (by unfold DOk; simp only [sC, sFn]; omega_arith) (by decide) k hr (fun e => absurd e (by decide))
    fun I e hFI => by
      have eB : p.B = I.B := (congrArg RpP.B e).symm
      have eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
      have hZ := h.ws.h256
      rw [eB] at hm
      rw [eZ] at hZ
      obtain ⟨a, b'⟩ := stab_writeW hF hZ (by decide) hFI hm k.2.1 k.2.2
      exact ⟨a, _, hz, b'⟩

theorem GD.mc {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w (fun I s => G I s ∧ MC I s) p s) :
    ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem [.mov .rcx (.mem (hdr sC))] c := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, z, hz, e⟩ := h
  exact ⟨z, hz, sC_pre h'.ws.h256 e⟩

theorem clzTop_ct {j : Nat} (hj : j < 16) (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8)
    (hw6 : ∀ p s, GD w F p s → 6 ≤ w p.k) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ (hOf ++
      (([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] : List Instr) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr)))))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.block (clzTop j)) (Two (GD w fun I s => F I s ∧ MC I s)) := by
  have e : clzTop j = ws ++ (base j .rbx ++ (hOf ++ (([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] :
      List Instr) ++ (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr))))) := by
    simp only [clzTop, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    exact WP.mono (clzTop_ok h.ws hj (hw6 p s h)) fun _ ⟨hm, k⟩ => h.setC (by omega_arith) hm k (by decide) hFc

theorem shlZ_ct {a d : Nat} (ha : a < 16) (hd : d < 16) (had : a ≠ d) {G : RpIn → State → Prop} (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (base a .r8 ++ (base d .rsi ++ (([.mov .rcx (.mem (hdr sC))] : List Instr) ++
      ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] : List Instr))))))
      (wordLoop 1 shlClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w fun I s => G I s ∧ MC I s)) (shlZ a d) (Two (GD w fun I s => G I s ∧ MC I s)) :=
  shlCl_ct false (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith) (sel_far a d had) (arr_mc hG)
    (fun _ _ h => h.mc) ht

theorem shrZ_ct {a d : Nat} (ha : a < 16) (hd : d < 16) (had : a ≠ d) {G : RpIn → State → Prop} (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .r8 ++ (base d .rsi ++
      ([.mov .rcx (.mem (hdr sC))] : List Instr)))) (wordLoop 0 shrClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w fun I s => G I s ∧ MC I s)) (shrZ a d) (Two (GD w fun I s => G I s ∧ MC I s)) :=
  shrCl_ct ha hd had (arr_mc hG) (fun _ _ h => h.mc) ht

theorem shlWordsF_ct {j c t : Nat} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hc64 : c ≤ 128) (hF : Arr F)
    (hw : ∀ p s, GD w F p s → c + 1 ≤ w p.k) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) hc₂).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shlWords false j c t)) (Two (GD w F)) := by
  have e : shlWords false j c t = [zeroA t, .seq (.block (ws ++ ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))))) copyWords] := by
    simp only [shlWords, wsW, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct ht' hF ht₁) (ct_one (copyP_ct hF
    (fun p => w p.k - c) (fun p => slot (w p.k) t + 8 * c) (fun p => slot (w p.k) j)
    (fun p s h => ?_) (fun p s h => ?_) ht₂))
  · have e' : ws ++ ((if false then wideR else []) ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++
        (base j .rsi ++ (base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))) =
        wsW false ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) := by
      simp only [wsW, List.append_assoc]
    rw [e']
    exact shlWBN_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) (j := j) (c := 1) (by omega_arith)
    have r2 := slot_room (w := w p.k) (j := t) (c := 1) (by omega_arith)
    have sep := slot_far (w := w p.k) hjt
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

theorem testTop_ct {j c : Nat} (hj : j < 16) (hc1 : 1 ≤ c) (hc64 : c ≤ 64)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) (hw : ∀ p s, GD wW F p s → c ≤ wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (seqs (testTop j c)) (Two (GD wW fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testTop j c) = .seq (.seq (.block (ws ++ (base j .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))))
      (wordLoop 0 or1Body)) (.block keepOf) := by
    simp only [testTop, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testTop_ok h.ws (wW_eq p.k) hj hc1 (hw p s h) hc64) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

/-- A stage of `c` words of `divB`'s normalization. -/
theorem stageD_ct {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₀ h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++
      ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr))) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 2 .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 2 .rsi ++ (base 3 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 5 .rsi ++ (base 3 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₃).isSome = true) :
    RelCT isa (Two (GD wW F)) (stageD c) (Two (GD wW F)) := by
  unfold stageD
  have e : ws ++ hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr) =
      ws ++ (hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr)) := by
    simp only [List.append_assoc]
  rw [e]
  refine stage_ct (cnd := fun p => decide (wk p.k < c + 1)) hF t₀ (fun p s h => by
    rw [← e]
    exact WP.mono (stageDHd_ok h.ws (wW_eq p.k) hc64) fun t ⟨⟨hcf, hm⟩, k⟩ =>
      ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG := hF.and (stab_const (Q := fun y => 256 ≤ y) fun I => c + 1 ≤ wk I.k)
  have hGB := arr_mb hG
  have hGb : Stab (fun I s => F I s ∧ c + 1 ≤ wk I.k) fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8 :=
    hFb.and (stab_const _)
  refine ct_pre (Ψ := GD wW fun I s => F I s ∧ c + 1 ≤ wk I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by simp only [decide_eq_false_iff_not] at hc; change ¬ wk I.k < c + 1 at hc; show c + 1 ≤ wk I.k; omega_arith⟩
  have hwk : ∀ p s, GD wW (fun I s => (F I s ∧ c + 1 ≤ wk I.k) ∧ MB I s) p s → c + 1 ≤ wk p.k := fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h
    exact hI.2
  have hT := testTop_ct (j := 2) (by decide) hc1 hc64 hGb (fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h
    have := hI.2; show c ≤ wk I.k; omega_arith) t₁
  have hS2 := shlWordsF_ct (j := 2) (t := 3) (w := wW) (by decide) (by decide) (by decide) (by omega_arith) hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₂
  have hK2 := selK_ct (w := wW) false (j := 2) (t := 3) (by decide) (by decide) (sel_far 2 3 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  have hS5 := shlWordsF_ct (j := 5) (t := 3) (w := wW) (by decide) (by decide) (by decide) (by omega_arith) hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₃
  have hK5 := selK_ct (w := wW) false (j := 5) (t := 3) (by decide) (by decide) (sel_far 5 3 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  exact ct_post (ct_app (by simp [testTop]) (List.cons_ne_nil _ _)
    (ct_app (by simp [testTop]) (by simp [shlWords])
      (ct_app (by simp [testTop]) (List.cons_ne_nil _ _)
        (ct_app (by simp [testTop]) (by simp [shlWords]) hT hS2) (ct_one hK2)) hS5) (ct_one hK5))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

/-- The divisor's top bit set: `qDiv`'s normalization. -/
def FD (I : RpIn) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem I.B (slot (wW I.k) qD + 8 * (wk I.k - 1))).toNat

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.add {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w F p s) (hG : ∀ I, pubD I = p → G I s) :
    GD w (fun I s => F I s ∧ G I s) p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
  exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, hG I rfl⟩

/-- `normDN`'s last block: the divisor's top bit set. -/
theorem forceTop_ct (hF : Arr F) :
    RelCT isa (Two (GD wW F)) (.block (ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr)))
      (Two (GD wW fun I s => F I s ∧ FD I s)) := by
  have e : ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr) =
      ws ++ (base 8 .r10 ++ (hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] :
        List Instr))) := by simp only [List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← e]
    have kb := h.kb
    have hw := h.ws
    have hn := hw.scr.nowrap
    have sl := slot_Z h (j := 8) (by decide)
    have e8 := slot_room (w := wW p.k) (j := 8) (c := 1) (by decide)
    have hWh := wW_eq p.k
    refine WP.mono (forceTop_ok hw hWh (by omega_arith)) fun t ⟨hm, k⟩ => ?_
    have o : Outside p.B (slot (wW p.k) 8 + 8 * (wk p.k - 1)) 8 s.mem t.mem := by
      rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
    refine (h.out o (by have := slot_256 (wW p.k) 8; omega_arith) (by omega_arith) k (by decide) hF).add
      fun I e' => ?_
    subst e'
    show 2 ^ 63 ≤ (word t.mem I.B (slot (wW I.k) qD + 8 * (wk I.k - 1))).toNat
    rw [hm]
    show 2 ^ 63 ≤ (word (s.mem.writeW (off I.B (slot (wW I.k) 8 + 8 * (wk I.k - 1))) _) I.B
      (slot (wW I.k) 8 + 8 * (wk I.k - 1))).toNat
    rw [word_writeW_self]
    exact top_or _

theorem normDN_ct (hF : Arr F) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    RelCT isa (Two (GD wW F)) (seqs normDN) (Two (GD wW fun I s => (F I s ∧ MC I s) ∧ FD I s)) := by
  have hS : ∀ c ∈ wordStages, RelCT isa (Two (GD wW F)) (stageD c) (Two (GD wW F)) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageD_ct (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  have hC := arr_mc hF
  unfold normDN
  exact ct_app (by simp [wordStages]) (List.cons_ne_nil _ _) (ct_map _ wordStages (by simp [wordStages]) hS)
    (ct_cons (List.cons_ne_nil _ _) (clzTop_ct (j := 2) (by decide) hFc (fun p s h => by
      have := h.kb; have := wW_eq p.k; omega_arith) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 8) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 2) (d := 8) (by decide) (by decide) (by decide) hF (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 9) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 5) (d := 9) (by decide) (by decide) (by decide) hF (by taint_decide))
    (ct_one (forceTop_ct hC)))))))

end

open VG.Impl.Rsa.X86_64.Keys.Recover (aE aD aM prodInit rowHead rowNext) in
/-- `prodB`'s loop, from `M = 0`, for what it changes. -/
theorem prodBLoop_frm {s : State} {B : Addr} {Z w u : Nat} (h : Ws s B Z w) (hwu : w = 2 * u + 2) (hu : 1 ≤ u)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * u))
    (hz : wv s.mem B (slot w aM) (2 * (w + 2)) = 0) :
    WP isa (.seq (.block (prodInit ++ ([.shift .shr .r12 1, .alu .sub .r12 (.imm 1)] : List Instr)))
      (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) s fun t =>
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (prodInit_ok h hel (by omega_arith))
    fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ =>
    WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 u ∧ t.mem = s₃.mem)
      (by xrun [h12, half1_ofNat (W := w) (by omega_arith) (by omega_arith), show w / 2 - 1 = u by omega_arith])
      rfl) fun s₄ ⟨⟨h12', m₄⟩, k₄⟩ => (show WP isa (.loop _ .ne) s₄ _ from ?_)))
  have hs₄ := h.scr.congr (k₃.trans k₄).2.2
  rw [show (8 * u + 7) / 8 = u by omega_arith] at h11
  refine wp_upto (a := 0) (N := u) hu (ProdInv s₄ B Z w u)
    (fun j _ hj t hI => prodStep_ok hI hu (by omega_arith) (by omega_arith) hZ (by omega_arith) hj h12'
      ((k₄.gpr (by decide)).trans hbx) ((k₄.gpr (by decide)).trans h10) ((k₄.gpr (by decide)).trans h15)
      ((k₄.gpr (by decide)).trans h11))
    (fun t hI => ?_) ⟨hs₄, Keep.refl _ _, (k₄.gpr (by decide)).trans h13, Outside.refl _ _ _ _,
      by rw [m₄, m₃, hz, wv, Nat.mul_zero]⟩
  exact ⟨fun x hx => by rw [hI.out x hx, m₄, m₃], ((k₃.trans k₄).trans hI.keep).mono (by simp [mmRegs])⟩

/-- The registers `prodB`'s loop needs pinned. -/
def prodBVal (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 (nv p.k)
  | .rbx => off p.B (slot (wW p.k) Recover.aE)
  | .r10 => off p.B (slot (wW p.k) Recover.aM)
  | .r15 => off p.B (slot (wW p.k) Recover.aD)
  | .r11 => BitVec.ofNat 64 (nv p.k)
  | .r13 => BitVec.ofNat 64 0
  | _ => 0

section
variable {F : RpIn → State → Prop}

theorem prodB_ct (hF : Arr F)
    (hel : ∀ p s, GD wW F p s → word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * nv p.k)) :
    RelCT isa (Two (GD wW F)) (seqs prodB) (Two (GD wW F)) := by
  simp only [prodB, seqs]
  refine RelCT.seq (zeroM_ct hF) (RelCT.seq (zeroM1_ct hF) ?_)
  refine pin_ct [.rdi] [.rdi, .r12, .rbx, .r10, .r15, .r11, .r13] prodBVal pins_GD (by taint_decide)
    (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have e1 := hel p s (h.mono fun _ _ h => h.1)
    have hw := h.ws
    have hw2 := hw.w2
    have hWv : wW p.k = 2 * nv p.k + 2 := rfl
    rw [WP.block_append_iff]
    refine WP.mono (prodInit_ok hw e1 (by omega_arith)) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (nv p.k))
      (by xrun [h12, half1_ofNat (W := wW p.k) (by omega_arith) (by omega_arith),
        show wW p.k / 2 - 1 = nv p.k by omega_arith]) rfl) fun t ⟨h12', k₄⟩ r hr => ?_
    rw [show (8 * nv p.k + 7) / 8 = nv p.k by omega_arith] at h11
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (k₄.gpr (by decide)).trans hdi
    · exact h12'
    · exact (k₄.gpr (by decide)).trans hbx
    · exact (k₄.gpr (by decide)).trans h10
    · exact (k₄.gpr (by decide)).trans h15
    · exact (k₄.gpr (by decide)).trans h11
    · exact (k₄.gpr (by decide)).trans h13
  · have e1 := hel p s (h.mono fun _ _ h => h.1)
    have hz : wv s.mem p.B (slot (wW p.k) Recover.aM) (2 * (wW p.k + 2)) = 0 := by
      obtain ⟨I, m₀, rfl, -, -, -, -, -, -, z⟩ := h; exact z
    have hw := h.ws
    have hWv : wW p.k = 2 * nv p.k + 2 := rfl
    have sl := hw.sl (j := Recover.aM + 1) (by decide)
    have eM1 : slot (wW p.k) (Recover.aM + 1) = slot (wW p.k) Recover.aM + 8 * (wW p.k + 2) := by
      simp only [Bignum.slot, hdrBytes, Recover.aM]; omega_arith
    exact WP.mono (prodBLoop_frm hw hWv (by simp only [nv]; omega_arith) e1 hz) fun t ⟨o, k⟩ =>
      (h.mono (F' := F) fun _ _ h => h.1).out o (slot_256 _ _) (by omega_arith) k (by decide) hF

end

end VG.Proof.Rsa.X86_64.Rd
