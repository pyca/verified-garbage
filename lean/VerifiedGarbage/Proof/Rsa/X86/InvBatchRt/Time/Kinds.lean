module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Step
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Virtualize
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Linear
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The batched inverse's operations, each in both runs

Each lemma is `relOp` for one kind of operation: the analysis's check of its instance, and the
operation's correctness, with its value forgotten, for the frame. Masks pass between neighbours
(`Mask`): an operation that leaves one in `ecx` gives any `X` that `Mask` implies.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)

/-- `ecx` a mask. -/
def Mask (g : Reg → BitVec 32) : Prop := ∃ k, g .ecx = cmask k

theorem mask_ite {g : Reg → BitVec 32} {p : Prop} [Decidable p]
    (h : g .ecx = if p then BitVec.allOnes 32 else 0) : Mask g :=
  ⟨decide p, by rw [h]; by_cases hp : p <;> simp [hp, cmask]⟩

/-- The writes of one range of the arrays. -/
theorem ws1 {o c Z : Nat} (ho : 104 ≤ o) (hz : o + c ≤ Z) :
    ∀ w ∈ [(o, c)], (104 ≤ w.1 ∨ w.1 + w.2 ≤ 100) ∧ w.1 + w.2 ≤ Z := by
  intro w hw
  simp only [List.mem_singleton] at hw
  subst w
  exact ⟨.inl ho, hz⟩

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G X : (Reg → BitVec 32) → Prop}

theorem relCopy {o a : Ref} {e : Nat} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (he : e ≤ 4) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + e) ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb _ => WP.mono (copy_ok hb he hoz haz sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relSelIn {o a : Ref} {e : Nat} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .edx, .ebp] G)
    (he : e ≤ 4) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len + e) ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (selIn L o a (nBytes .edi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ Mask g) (selIn L o a (nBytes .edi e))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb ⟨k, hk⟩ => WP.mono (selIn_ok hb hk he hoz haz sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relZeros {o : Ref} {cnt : List Instr} {c : Nat} (hL : L.ws = 14) (hG : Stable [.eax, .ecx, .edx, .ebp] G)
    (hcs : ∀ s, Bx L s B Z len N → CountSpec cnt .ecx B Z (kw len) c) (hc0 : 0 < c)
    (hoz : rv (kw len) o + 4 * c ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt)
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb _ => WP.mono (zeros_ok hb (hcs s hb) hc0 hoz) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- `nBytes .ecx 1` counts `n + 1` words. -/
theorem countN {s : State} (hb : Bx L s B Z len N) : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
  have := nBytes_spec (r := .ecx) (e := 1) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega)
    (by decide) (by have := kw_eq len; omega)
  rwa [show kw len / 2 + 1 = nw len + 1 by have := kw_eq len; omega] at this

/-- `wBytes .ecx` counts `w` words. -/
theorem countW {s : State} (hb : Bx L s B Z len N) : CountSpec (wBytes .ecx) .ecx B Z (kw len) (kw len) :=
  wBytes_spec hb.halfZ (by have := kw_bound hb.ws.lenLe; omega)

theorem relZeroWord {x : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .edx] G) (hxz : rv (kw len) x + 4 ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (zeroWord L x)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (zeroWord L x))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) x; omega) hxz)
    (fun s hb _ => by
      rw [show zeroWord L x = zeroWord L x ++ [] from (List.append_nil _).symm]
      exact zeroWord_ok hb hxz fun u H K O _ => WP.block_nil ⟨H, K, O.unch, trivial⟩) h

theorem relChainAdd {o a b : Ref} {e : Nat} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hX : ∀ g, Mask g → X g) (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (da : rv (kw len) o ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    (db : rv (kw len) o ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e))
      (Both L B Z len N args sp C fun g => G g ∧ X g) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb _ => WP.mono (chainAdd_ok hb he hoh hoz haz hbz da db) fun _ ⟨H, O, ⟨c, hc, _⟩, K⟩ =>
      ⟨H, K, O.unch, hX _ ⟨c, hc⟩⟩) h

theorem relChainSub {o a b : Ref} {e : Nat} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hX : ∀ g, Mask g → X g) (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * (nw len + e) ≤ Z) (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z)
    (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (da : rv (kw len) o ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) o)
    (db : rv (kw len) o ≤ rv (kw len) b ∨ rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e))
      (Both L B Z len N args sp C fun g => G g ∧ X g) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb _ => WP.mono (chainSub_ok hb he hoh hoz haz hbz da db) fun _ ⟨H, O, ⟨c, hc, _⟩, K⟩ =>
      ⟨H, K, O.unch, hX _ ⟨c, hc⟩⟩) h

theorem relMaskAt {x : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx] G) (hxz : rv (kw len) x + 4 ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (maskAt L x)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (maskAt L x))
      (Both L B Z len N args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) hL (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => by
      rw [show maskAt L x = maskAt L x ++ [] from (List.append_nil _).symm]
      exact maskAt_ok hb hxz fun u K m c => WP.block_nil ⟨hb.keep K (by decide) (by decide)
        (by rw [m]; exact Outside.refl _ _ _ _) (rv_ge _ x) hxz, K, by rw [m]; exact Unch.refl _ _ _, mask_ite c⟩) h

/-- `maskAt x` and its complement. -/
theorem relMaskAtNot {x : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx] G)
    (hxz : rv (kw len) x + 4 ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (maskAt L x ++ [.alu .xor .ecx (.imm (-1))])) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (.block (maskAt L x ++ [.alu .xor .ecx (.imm (-1))]))
      (Both L B Z len N args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) hL (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => maskAt_ok hb hxz fun u K m c => wp_logicS (.inr rfl) rfl fun t U => WP.block_nil ⟨hb.keep
      (K.trans (U.keeps.mono (by decide))) (by decide) (by decide) (by rw [U.mem, m]; exact Outside.refl _ _ _ _)
      (rv_ge _ x) hxz, K.trans (U.keeps.mono (by decide)), by rw [U.mem, m]; exact Unch.refl _ _ _, by
        refine ⟨!decide (2 ^ 31 ≤ w32 s.mem B (rv (kw len) x)), ?_⟩
        have e := U.gpr
        simp only [reduceCtorEq, ite_false] at e
        rw [e, c]
        split <;> simp_all [cmask]⟩) h

theorem relEvenMask (hL : L.ws = 14) (hG : Stable [.ecx] G) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask
      (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0))) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True)
      (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0)))
      (Both L B Z len N args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) hL (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok hb.ws.ws.workspace
      (src := VG.Impl.Rsa.X86.InvBatchRt.offset 0 0) (by
        have := hb.fits16; simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega)) fun t ⟨c, K, m⟩ =>
      ⟨hb.keep K (by decide) (by decide) (o := 160) (c := 0) (by rw [m]; exact Outside.refl _ _ _ _) (Nat.le_refl _)
        (by have := hb.fits16; omega), K, by rw [m]; exact Unch.refl _ _ _, mask_ite c⟩) h

theorem relVirtualize (hL : L.ws = 14) (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G) (hn2 : 2 ≤ nw len)
    (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (virtualize L) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (virtualize L)
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_a len 2; omega) (by have := rv_a len 2; omega))
    (fun s hb _ => WP.mono (virtualize_ok hb hn2) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem rowAdd_frame {set : Bool} {s : State} (h : Bx L s B Z len N) {c : Nat} (hc : c + 4 ≤ 160)
    {acc src : Ref} {e : Nat} (he : e ≤ 4) (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src) :
    WP isa (rowAdd L set c acc src (nBytes .esi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem t.mem ∧
      Keeps VG.Proof.Weierstrass.X86.Inv.wordClob s t := by
  have ra := rv_ge (kw len) acc
  unfold rowAdd
  refine WP.seq (wp_movS (readSrc_sc h.ws.ws.workspace (d := c) (by omega)) fun u U _ => WP.block_nil ?_)
  have hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  exact WP.mono (mulRow_gen hu he hsh haz hsz sep) fun t ⟨H, O, _, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

theorem relRowAdd {set : Bool} {c : Nat} {acc src : Ref} {e : Nat} (hL : L.ws = 14)
    (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G) (hc4 : c + 4 ≤ 160) (he : e ≤ 4) (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (rowAdd L set c acc src (nBytes .esi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (rowAdd L set c acc src (nBytes .esi e))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) acc; omega) haz)
    (fun s hb _ => WP.mono (rowAdd_frame hb hc4 he hsh haz hsz sep) fun _ ⟨H, O, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- A coefficient's sign, then the selection of a correction into `[acc + 4]`. -/
theorem relMaskOfSel {c : Nat} {acc tmp : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hc4 : c + 4 ≤ 160) (haz : rv (kw len) acc + 4 * (nw len + 1) ≤ Z) (htz : rv (kw len) tmp + 4 * nw len ≤ Z)
    (ta : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c))
      (selIn L { acc with byte := acc.byte + 4 } tmp (nBytes .edi 0))) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True)
      (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c)) (selIn L { acc with byte := acc.byte + 4 } tmp (nBytes .edi 0)))
      (Both L B Z len N args sp C fun g => G g ∧ True) := by
  have e4 := rv_byte (kw len) acc 4
  refine relOp (ws := [(rv (kw len) acc + 4, 4 * nw len)]) hL (by decide) hG
    (ws1 (by have := rv_ge (kw len) acc; omega) (by omega)) (fun s hb _ => ?_) h
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.X86.Inv.maskOf_ok hb.ws.ws.workspace (coefficient := c) (by
    have := hb.fits16; omega)) fun s₂ ⟨M₂, K₂, m₂⟩ => ?_)
  have H₂ : Bx L s₂ B Z len N := hb.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  refine WP.mono (selIn_ok H₂ (o := { acc with byte := acc.byte + 4 }) (a := tmp) (e := 0)
    (k := decide (2 ^ 31 ≤ w32 s.mem B c)) (by rw [M₂]; simp [cmask]) (by decide)
    (by rw [e4]; omega) (by simpa using htz) (by rw [e4]; omega)) fun u ⟨H, O, _, K⟩ => ?_
  rw [e4] at O
  simp only [Nat.add_zero] at O
  exact ⟨H, (K₂.mono (by decide)).trans (K.mono (by decide)), by rw [m₂] at O; exact O.unch, trivial⟩

theorem relShr30 {dst src : Ref} (hL : L.ws = 14) (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G)
    (hdh : dst.half = 0) (hev : nw len % 2 = 0) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint τS (shr30 L dst src) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (shr30 L dst src)
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) dst; omega) hdz)
    (fun s hb _ => WP.mono (shr30_ok hb hdh hev hsz hdz sep) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relNegTop {acc : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G) (hah : acc.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + 1) ≤ Z) (htz : rv (kw len) tmp + 4 * (nw len + 1) ≤ Z)
    (sta : rv (kw len) tmp + 4 * (nw len + 1) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint τS (.block (negTop L acc)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ Mask g) (.block (negTop L acc))
      (Both L B Z len N args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := [(rv (kw len) tmp + 4 * nw len, 4)]) hL (by decide) hG
    (ws1 (by have := rv_ge (kw len) tmp; omega) (by omega))
    (fun s hb ⟨k, hk⟩ => by
      rw [show negTop L acc = negTop L acc ++ [] from (List.append_nil _).symm]
      exact negTop_ok hb hah haz htz sta hk fun u H K O _ c => WP.block_nil ⟨H, K, O.unch, mask_ite c⟩) h

theorem relBorrowMask {src : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .ecx, .edx] G) (hsh : src.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.block (borrowMask L src)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ Mask g) (.block (borrowMask L src))
      (Both L B Z len N args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) hL (by decide) hG (fun _ h => nomatch h)
    (fun s hb ⟨k, hk⟩ => by
      rw [show borrowMask L src = borrowMask L src ++ [] from (List.append_nil _).symm]
      exact borrowMask_ok hb hsh hsz hk fun u H K m c => WP.block_nil
        ⟨H, K, by rw [m]; exact Unch.refl _ _ _, ⟨_, c⟩⟩) h

theorem relSelect3 {o a b : Ref} (hL : L.ws = 14) (hG : Stable [.eax, .ebx, .edx, .ebp] G)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * nw len ≤ Z) (haz : rv (kw len) a + 4 * nw len ≤ Z)
    (hbz : rv (kw len) b + 4 * nw len ≤ Z)
    (soa : rv (kw len) o + 4 * nw len ≤ rv (kw len) a ∨ rv (kw len) a + 4 * nw len ≤ rv (kw len) o)
    (sob : rv (kw len) o + 4 * nw len ≤ rv (kw len) b ∨ rv (kw len) b + 4 * nw len ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint τS (.seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx 0 ++
      ptr L .edi o .eax)) (.seq select3LoopX (.block (restoreEdi L)))) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ Mask g)
      (.seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
        (.seq select3LoopX (.block (restoreEdi L))))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp hL (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb ⟨k, hk⟩ => WP.mono (select3_ok hb hk hoh hoz haz hbz soa sob) fun _ ⟨H, O, _, K⟩ =>
      ⟨H, K, O.unch, trivial⟩) h

end VG.Proof.Rsa.X86.InvBatchRt.Time
