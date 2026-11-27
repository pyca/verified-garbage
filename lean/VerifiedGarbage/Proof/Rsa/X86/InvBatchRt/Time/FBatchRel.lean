module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FRowRel
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Impl.Weierstrass.X86.Inv
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.RowOp
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Virtualize
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.InitWords
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift

/-! ### `Rsa.X86.InvBatchRt.Time.Kinds2`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.InvBatchRt.Time.Kinds`, which this module and modules that import it used -/

section

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

variable {L : Lay} {B : Addr} {Z len N n : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G X : (Reg → BitVec 32) → Prop}

theorem relCopy {o a : Ref} {e : Nat} (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (he : e ≤ 4) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (sep : rv (kw len) o n + 4 * (n + e) ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytes .edi e))
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o n; omega_using [this]) hoz)
    (fun s hb _ => WP.mono (copy_ok hb he hoz haz sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relSelIn {o a : Ref} {e : Nat} (hG : Stable [.eax, .ebx, .edx, .ebp] G)
    (he : e ≤ 4) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (sep : rv (kw len) o n + 4 * (n + e) ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (selIn L o a (nBytes .edi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ Mask g) (selIn L o a (nBytes .edi e))
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o n; omega_using [this]) hoz)
    (fun s hb ⟨k, hk⟩ => WP.mono (selIn_ok hb hk he hoz haz sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relZeros {o : Ref} {cnt : List Instr} {c : Nat} (hG : Stable [.eax, .ecx, .edx, .ebp] G)
    (hcs : ∀ s, Bx L s B Z len N n → CountSpec cnt .ecx B Z (kw len) c n) (hc0 : 0 < c)
    (hoz : rv (kw len) o n + 4 * c ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.zeros L o cnt)
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o n; omega_using [this]) hoz)
    (fun s hb _ => WP.mono (zeros_ok hb (hcs s hb) hc0 hoz) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- `nBytes .ecx 1` counts `n + 1` words. -/
theorem countN {s : State} (hb : Bx L s B Z len N) : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
  have := nBytes_spec (r := .ecx) (e := 1) (B := B) hb.halfZ (w := kw len) (by have := kw_bound hb.ws.lenLe; omega_using [this])
    (by decide) (by have := kw_eq len; omega_using [this])
  rwa [show kw len / 2 + 1 = nw len + 1 by have := kw_eq len; omega_using [this]] at this

/-- `nBytes .ecx 1` counts `n + 1` words, for rows of any `n` words. -/
theorem countN_of {s : State} (hb : Bx L s B Z len N n) (hn : 4 * n + 16 < 2 ^ 32) :
    CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (n + 1) n :=
  nBytesN_spec hb.halfZ hn (by decide)

/-- `wBytes .ecx` counts `w` words. -/
theorem countW {s : State} (hb : Bx L s B Z len N) : CountSpec (wBytes .ecx) .ecx B Z (kw len) (kw len) :=
  wBytes_spec hb.halfZ (by have := kw_bound hb.ws.lenLe; omega_using [this]) (by have := kw_eq len; omega_using [this])

theorem relZeroWord {x : Ref} (hG : Stable [.eax, .ebx, .edx] G) (hxz : rv (kw len) x n + 4 ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (zeroWord L x)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (.block (zeroWord L x))
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) x n; omega_using [this]) hxz)
    (fun s hb _ => by
      rw [show zeroWord L x = zeroWord L x ++ [] from (List.append_nil _).symm]
      exact zeroWord_ok hb hxz fun u H K O _ => WP.block_nil ⟨H, K, O.unch, trivial⟩) h

theorem relChainAdd {o a b : Ref} {e : Nat} (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hX : ∀ g, Mask g → X g) (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (hbz : rv (kw len) b n + 4 * (n + e) ≤ Z)
    (da : rv (kw len) o n ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    (db : rv (kw len) o n ≤ rv (kw len) b n ∨ rv (kw len) b n + 4 * (n + e) ≤ rv (kw len) o n)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.chain L .adc o a b (nBytes .edx e))
      (Both L B Z len N n args sp C fun g => G g ∧ X g) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o n; omega_using [this]) hoz)
    (fun s hb _ => WP.mono (chainAdd_ok hb he hoh hoz haz hbz da db) fun _ ⟨H, O, ⟨c, hc, _⟩, K⟩ =>
      ⟨H, K, O.unch, hX _ ⟨c, hc⟩⟩) h

theorem relChainSub {o a b : Ref} {e : Nat} (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hX : ∀ g, Mask g → X g) (he : e ≤ 4)
    (hoh : o.half = 0) (hoz : rv (kw len) o n + 4 * (n + e) ≤ Z) (haz : rv (kw len) a n + 4 * (n + e) ≤ Z)
    (hbz : rv (kw len) b n + 4 * (n + e) ≤ Z)
    (da : rv (kw len) o n ≤ rv (kw len) a n ∨ rv (kw len) a n + 4 * (n + e) ≤ rv (kw len) o n)
    (db : rv (kw len) o n ≤ rv (kw len) b n ∨ rv (kw len) b n + 4 * (n + e) ≤ rv (kw len) o n)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb o a b (nBytes .edx e))
      (Both L B Z len N n args sp C fun g => G g ∧ X g) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o n; omega_using [this]) hoz)
    (fun s hb _ => WP.mono (chainSub_ok hb he hoh hoz haz hbz da db) fun _ ⟨H, O, ⟨c, hc, _⟩, K⟩ =>
      ⟨H, K, O.unch, hX _ ⟨c, hc⟩⟩) h

theorem relMaskAt {x : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx] G) (hxz : rv (kw len) x n + 4 ≤ Z)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (maskAt L x)) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (.block (maskAt L x))
      (Both L B Z len N n args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => by
      rw [show maskAt L x = maskAt L x ++ [] from (List.append_nil _).symm]
      exact maskAt_ok hb hxz fun u K m c => WP.block_nil ⟨hb.keep K (by decide) (by decide)
        (by rw [m]; exact Outside.refl _ _ _ _) (rv_ge _ x n) hxz, K, by rw [m]; exact Unch.refl _ _ _, mask_ite c⟩) h

/-- `maskAt x` and its complement. -/
theorem relMaskAtNot {x : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx] G)
    (hxz : rv (kw len) x n + 4 ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (maskAt L x ++ ([.alu .xor .ecx (.imm (-1))] : List Instr))) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (.block (maskAt L x ++ ([.alu .xor .ecx (.imm (-1))] : List Instr)))
      (Both L B Z len N n args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => maskAt_ok hb hxz fun u K m c => wp_logicS (.inr rfl) rfl fun t U => WP.block_nil ⟨hb.keep
      (K.trans (U.keeps.mono (by decide))) (by decide) (by decide) (by rw [U.mem, m]; exact Outside.refl _ _ _ _)
      (rv_ge _ x n) hxz, K.trans (U.keeps.mono (by decide)), by rw [U.mem, m]; exact Unch.refl _ _ _, by
        refine ⟨!decide (2 ^ 31 ≤ w32 s.mem B (rv (kw len) x n)), ?_⟩
        have e := U.gpr
        simp only [reduceCtorEq, ite_false] at e
        rw [e, c]
        split <;> simp_all [cmask]⟩) h

theorem relEvenMask (hG : Stable [.ecx] G) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask
      (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0))) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True)
      (.block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0)))
      (Both L B Z len N n args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) (by decide) hG (fun _ h => nomatch h)
    (fun s hb _ => WP.mono (VG.Proof.Rsa.X86.GcdBatch.evenMask_ok hb.ws.ws.workspace
      (src := VG.Impl.Rsa.X86.InvBatchRt.offset 0 0) (by
        have := hb.fits16; simp only [VG.Impl.Rsa.X86.InvBatchRt.offset]; omega_using [this])) fun t ⟨c, K, m⟩ =>
      ⟨hb.keep K (by decide) (by decide) (o := 160) (c := 0) (by rw [m]; exact Outside.refl _ _ _ _) (Nat.le_refl _)
        (by have := hb.fits16; omega_using [this]), K, by rw [m]; exact Unch.refl _ _ _, mask_ite c⟩) h

theorem relVirtualize (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G) (hn2 : 2 ≤ nw len)
    (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (virtualize L) hc).isSome = true) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) (virtualize L)
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_a len 2; omega_using [this]) (by have := rv_a len 2; omega_using [hfit, this]))
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
  refine WP.seq (wp_movS (readSrc_sc h.ws.ws.workspace (d := c) (by omega_using [hc, haz, ra])) fun u U _ => WP.block_nil ?_)
  have hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  exact WP.mono (mulRow_gen hu he hsh haz hsz sep) fun t ⟨H, O, _, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

theorem relRowAdd {set : Bool} {c : Nat} {acc src : Ref} {e : Nat}
    (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G) (hc4 : c + 4 ≤ 160) (he : e ≤ 4) (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (rowAdd L set c acc src (nBytes .esi e)) hc).isSome = true) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) (rowAdd L set c acc src (nBytes .esi e))
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) acc; omega_using [this]) haz)
    (fun s hb _ => WP.mono (rowAdd_frame hb hc4 he hsh haz hsz sep) fun _ ⟨H, O, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- A coefficient's sign, then the selection of a correction into `[acc + 4]`. -/
theorem relMaskOfSel {c : Nat} {acc tmp : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hc4 : c + 4 ≤ 160) (haz : rv (kw len) acc n + 4 * (n + 1) ≤ Z) (htz : rv (kw len) tmp n + 4 * n ≤ Z)
    (ta : rv (kw len) tmp n + 4 * n ≤ rv (kw len) acc n ∨ rv (kw len) acc n + 4 * (n + 1) ≤ rv (kw len) tmp n)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c))
      (selIn L { acc with byte := acc.byte + 4 } tmp (nBytes .edi 0))) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True)
      (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c)) (selIn L { acc with byte := acc.byte + 4 } tmp (nBytes .edi 0)))
      (Both L B Z len N n args sp C fun g => G g ∧ True) := by
  have e4 := rv_byte (kw len) acc 4 n
  refine relOp (ws := [(rv (kw len) acc n + 4, 4 * n)]) (by decide) hG
    (ws1 (by have := rv_ge (kw len) acc n; omega_using [this]) (by omega_using [haz])) (fun s hb _ => ?_) h
  refine WP.seq (WP.mono (VG.Proof.Weierstrass.X86.Inv.maskOf_ok hb.ws.ws.workspace (coefficient := c) (by
    have := hb.fits16; omega_using [hc4, this])) fun s₂ ⟨M₂, K₂, m₂⟩ => ?_)
  have H₂ : Bx L s₂ B Z len N n := hb.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc n) haz
  refine WP.mono (selIn_ok H₂ (o := { acc with byte := acc.byte + 4 }) (a := tmp) (e := 0)
    (k := decide (2 ^ 31 ≤ w32 s.mem B c)) (by rw [M₂]; simp [cmask]) (by decide)
    (by rw [e4]; have := kw_eq len; omega_using [haz]) (by simpa using htz) (by rw [e4]; have := kw_eq len; omega_using [ta])) fun u ⟨H, O, _, K⟩ => ?_
  rw [e4] at O
  simp only [Nat.add_zero] at O
  exact ⟨H, (K₂.mono (by decide)).trans (K.mono (by decide)), by rw [m₂] at O; exact O.unch, trivial⟩

theorem relBorrowMask {src : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx] G) (hsh : src.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (borrowMask L src)) hc).isSome = true) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ Mask g) (.block (borrowMask L src))
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ Mask g) :=
  relOp (ws := []) (by decide) hG (fun _ h => nomatch h)
    (fun s hb ⟨k, hk⟩ => by
      rw [show borrowMask L src = borrowMask L src ++ [] from (List.append_nil _).symm]
      exact borrowMask_ok hb hsh hsz hk fun u H K m c => WP.block_nil
        ⟨H, K, by rw [m]; exact Unch.refl _ _ _, ⟨_, c⟩⟩) h

theorem relSelect3 {o a b : Ref} (hG : Stable [.eax, .ebx, .edx, .ebp] G)
    (hoh : o.half = 0) (hoz : rv (kw len) o + 4 * nw len ≤ Z) (haz : rv (kw len) a + 4 * nw len ≤ Z)
    (hbz : rv (kw len) b + 4 * nw len ≤ Z)
    (soa : rv (kw len) o + 4 * nw len ≤ rv (kw len) a ∨ rv (kw len) a + 4 * nw len ≤ rv (kw len) o)
    (sob : rv (kw len) o + 4 * nw len ≤ rv (kw len) b ∨ rv (kw len) b + 4 * nw len ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx 0 ++
      ptr L .edi o .eax)) (.seq select3LoopX (.block (restoreEdi L)))) hc).isSome = true) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ Mask g)
      (.seq (.block (ptr L .ebp a .edx ++ ptr L .ebx b .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
        (.seq select3LoopX (.block (restoreEdi L))))
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega_using [this]) hoz)
    (fun s hb ⟨k, hk⟩ => WP.mono (select3_ok hb hk hoh hoz haz hbz soa sob) fun _ ⟨H, O, _, K⟩ =>
      ⟨H, K, O.unch, trivial⟩) h

end VG.Proof.Rsa.X86.InvBatchRt.Time

end

end

/-! # The batched inverse's header operations, each in both runs

The slots (from `Pre0`), the start of the state and its count, the inverse word, the windows'
steps, and the batch count down by one, whose flags agree.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

/-- `Dynamic.inverse` writes only registers. -/
theorem inverse_frame (s : State) :
    WP isa (.block VG.Impl.Mont.X86.Dynamic.inverse) s fun t => Keeps [.eax, .ecx, .edx, .ebp] s t ∧ t.mem = s.mem := by
  unfold VG.Impl.Mont.X86.Dynamic.inverse
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun t₀ u₀ _ => ?_
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₀) fun t₁ ⟨_, k₁, m₁⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₁) fun t₂ ⟨_, k₂, m₂⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₂) fun t₃ ⟨_, k₃, m₃⟩ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.newton_ok t₃) fun t₄ ⟨_, k₄, m₄⟩ => ?_)
  refine wp_movS rfl fun t₅ u₅ _ => wp_subS rfl fun t₆ u₆ _ => WP.block_nil ⟨?_, ?_⟩
  · exact (((((u₀.keeps.mono (by decide)).trans k₁).trans k₂).trans k₃).trans k₄ |>.widen u₅.keeps).widen u₆.keeps
  · rw [u₆.mem, u₅.mem, m₄, m₃, m₂, m₁, u₀.mem]

variable {L : Lay} {B : Addr} {Z len N n : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G : (Reg → BitVec 32) → Prop}

theorem relSlots {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τ0 L) (.block (slots L)) hc).isSome = true) :
    RelCT isa (fun s t => Pre0 L B Z len N args sp s ∧ Pre0 L B Z len N args sp t) (.block (slots L))
      (Both L B Z len N (nw len) args sp (fun _ => True) fun _ => True ∧ True) :=
  leaf0 (fun s ps => by
    rw [show slots L = slots L ++ [] from (List.append_nil _).symm]
    exact slots_ok ps.1 ps.2.1 fun u H K O => WP.block_nil ⟨H, ps.2.2.keep K (by decide)
      (O.mono (Nat.zero_le _) (by have := H.halfZ; simp only [slotBase, halfSlot] at this ⊢; omega_using [this])),
      trivial, trivial, trivial⟩) h

/-- `delta = 1`. -/
theorem relWinOne (hG : Stable [.eax] G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block [.mov .eax (.imm 1), .store (sc win) .eax]) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (.block [.mov .eax (.imm 1), .store (sc win) .eax])
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win, 4)]) (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega_using [hfit]⟩)
    (fun s hb _ => by
      have hZ := hb.halfZ
      refine wp_movS rfl fun u₁ V₁ _ => ?_
      have hs₁ := hb.ws.ws.workspace.of_keeps V₁.keeps (by decide)
      refine wp_storeS (hs₁.ea (by simp only [win, halfSlot] at hZ ⊢; omega_using [hfit]))
        (hs₁.write (d := win) (n := 4) (by simp only [win, halfSlot] at hZ ⊢; omega_using [hfit])) fun u₂ V₂ => WP.block_nil ?_
      have O₂ : Outside B win 4 s.mem u₂.mem := by
        rw [V₂.mem, V₁.mem]; exact writeW32_outside _ _ _ (by have := hb.nowrap; simp only [win]; omega_using [])
      exact ⟨hb.keepLow (V₁.keeps.trans (V₂.keeps _)) (by decide) (by decide) O₂ (by decide),
        V₁.keeps.trans (V₂.keeps _), O₂.unch, trivial⟩) h

/-- The inverse word, from `[2]`'s low word. -/
theorem relInverse (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G)
    (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (ptr L .eax (a 2) .edx ++ ([.mov .ebx (.mem (at_ .eax 0))] : List Instr) ++
      VG.Impl.Mont.X86.Dynamic.inverse ++ ([.store (sc (win + 28)) .eax] : List Instr))) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True)
      (.block (ptr L .eax (a 2) .edx ++ ([.mov .ebx (.mem (at_ .eax 0))] : List Instr) ++
        VG.Impl.Mont.X86.Dynamic.inverse ++ ([.store (sc (win + 28)) .eax] : List Instr)))
      (Both L B Z len N n args sp C fun g => G g ∧ True) := by
  have r2 : rv (kw len) (a 2) n = 160 + 2 * (8 * nw len + 8) := (rv_h0 rfl n (kw len / 2)).trans (rv_a len 2)
  refine relOp (ws := [(win + 28, 4)]) (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega_using [hfit]⟩)
    (fun s hb _ => ?_) h
  have hn := hb.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok hb.ws hb.slots hb.halfZ (r := .eax) (t := .edx) (x := a 2) (by decide) (by decide) (by decide)
    (by decide) (by intro e; cases e) (by omega_using [hfit, r2, hn]) fun u₈ K₈ m₈ p₈ => ?_
  have hw₈ := hb.ws.rt.of_keeps K₈
  refine wp_movS (readSrc_ptr hw₈ p₈ (d := 0) (by omega_using [hfit, r2])) fun u₉ V₉ _ => ?_
  refine WP.block_append (WP.mono (inverse_frame u₉) fun u₁₀ ⟨K₁₀, M₁₀⟩ => ?_)
  have K₁₀' : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u₁₀ :=
    ((K₈.mono (by decide)).trans (V₉.keeps.mono (by decide))).trans (K₁₀.mono (by decide))
  have hs₁₀ := hb.ws.ws.workspace.of_keeps K₁₀' (by decide)
  refine wp_storeS (hs₁₀.ea (by simp only [win]; omega_using [hfit])) (hs₁₀.write (d := win + 28) (n := 4) (by simp only [win]; omega_using [hfit]))
    fun u₁₁ V₁₁ => WP.block_nil ?_
  have O₁₁ : Outside B (win + 28) 4 s.mem u₁₁.mem := by
    rw [V₁₁.mem, M₁₀, V₉.mem, m₈]; exact writeW32_outside _ _ _ (by simp only [win]; omega_using [])
  exact ⟨hb.keepLow (K₁₀'.trans (V₁₁.keeps _)) (by decide) (by decide) O₁₁ (by decide), K₁₀'.trans (V₁₁.keeps _),
    O₁₁.unch, trivial⟩

/-- The batch count, `3 (n + 1)`. -/
theorem relBatches (hG : Stable [.eax, .ecx] G) (hn4 : 4 * n + 16 < 2 ^ 32) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block batches) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (.block batches)
      (Both L B Z len N n args sp (· = 3 * (n + 1)) fun g => G g ∧ True) :=
  leafU (fun s ps => by
    have hb := ps.1
    have hn := hb.nowrap
    have hZ := hb.halfZ
    have hf16 := hb.fits16
    unfold batches
    refine nBytes_ok hb.ws.ws.workspace hb.slots hZ hn4 (e := 1) (by decide) fun u₁₂ K₁₂ m₁₂ c₁₂ => ?_
    refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₁₃ V₁₃ => ?_
    refine wp_movS rfl fun u₁₄ V₁₄ _ => wp_addS rfl fun u₁₅ V₁₅ _ => wp_addS rfl fun u₁₆ V₁₆ _ => ?_
    have K₁₆ : Keeps [.eax, .ecx] s u₁₆ :=
      ((((K₁₂.mono (by decide)).trans (V₁₃.keeps.mono (by decide))).trans (V₁₄.keeps.mono (by decide))).trans
        (V₁₅.keeps.mono (by decide))).trans (V₁₆.keeps.mono (by decide))
    have hs₁₆ := hb.ws.ws.workspace.of_keeps K₁₆ (by decide)
    refine wp_storeS (hs₁₆.ea (by omega_using [hf16])) (hs₁₆.write (d := 100) (n := 4) (by omega_using [hf16])) fun z Vz => WP.block_nil ?_
    have m₁₆ : u₁₆.mem = s.mem := by rw [V₁₆.mem, V₁₅.mem, V₁₄.mem, V₁₃.mem, m₁₂]
    have Oz : Outside B 100 4 s.mem z.mem := by rw [Vz.mem, m₁₆]; exact writeW32_outside _ _ _ (by omega_using [])
    have Kz := K₁₆.trans (Vz.keeps _)
    refine ⟨hb.keepHigh Kz (by decide) (by decide) Oz (by decide) (by omega_using [hf16]),
      ps.2.1.keep Kz (by decide) (Oz.mono (Nat.zero_le _) (by omega_using [hf16])), ?_, hG _ _ Kz.1 ps.2.2.2.1, trivial⟩
    show w32 z.mem B 100 = 3 * (n + 1)
    rw [Vz.mem, w32_write_self, V₁₆.gpr, V₁₅.gpr, V₁₅.other .ecx (by decide), V₁₄.gpr, V₁₄.other _ (by decide),
      V₁₃.gpr]
    have e₁₂ : (u₁₂.gpr .eax).toNat = 4 * (n + 1) := by rw [c₁₂]; omega_using []
    have e₁₃ : (u₁₂.gpr .eax >>> 2).toNat = n + 1 := by
      rw [BitVec.toNat_ushiftRight, e₁₂, Nat.shiftRight_eq_div_pow]; omega_using []
    simp only [BitVec.toNat_add, e₁₃]
    omega_using [hn4]) h

theorem relStart (hG : Stable wordClob G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block (start L)) hc).isSome = true) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) (.block (start L))
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win + 4, 24)]) (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega_using [hfit]⟩)
    (fun s hb _ => WP.mono (start_ok hb) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relWordSteps (hG : Stable wordClob G) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp C fun g => G g ∧ True) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)
      (Both L B Z len N n args sp C fun g => G g ∧ True) :=
  relOp (ws := [(win, 28)]) (by decide) hG (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega_using [hfit]⟩)
    (fun s hb _ => WP.mono (VG.Proof.Weierstrass.X86.Inv.wordSteps_ok hb.ws.ws.workspace (t := win)
      (by have := hb.halfZ; simp only [win, halfSlot] at this ⊢; omega_using [hfit]) (by decide) (by decide))
      fun t ⟨_, K, O⟩ => ⟨hb.keepLow K (by decide) (by decide) O (by decide), K, O.unch, trivial⟩) h

/-- The batch count down by one, its flags set by the new count. -/
theorem relCountDown {m : Nat} (hm : 1 ≤ m) (hm32 : m < 2 ^ 32) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi,
      testCounter]) hc).isSome = true) :
    RelCT isa (Both L B Z len N n args sp (· = m) fun _ => True ∧ True)
      (.block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter])
      (fun s t => Both L B Z len N n args sp (· = m - 1) (fun _ => True ∧ True) s t ∧
        s.zf = some (decide (m - 1 = 0)) ∧ t.zf = some (decide (m - 1 = 0))) :=
  (leafU (Q := fun t => Pre L B Z len N n args sp (fun g m' => (· = m - 1) (w32 m' B 100) ∧ True ∧ True) t ∧
      t.zf = some (decide (m - 1 = 0))) (fun s ps => by
    have hb := ps.1
    have hZ := hb.halfZ
    have hf16 := hb.fits16
    exact WP.mono (VG.Proof.Rsa.X86.GcdBatch.countDown_ok hb.ws.ws.workspace (d := 100)
      (by simp only [halfSlot] at hZ; omega_using [hf16]) hm hm32 ps.2.2.1) fun z ⟨c, zf, K, O⟩ =>
      ⟨⟨hb.keepHigh K (by decide) (by decide) O (by decide) (by omega_using [hf16]),
        ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega_using [hf16])), c, trivial, trivial⟩, zf⟩) h).mono
    (fun _ _ h => h) fun _ _ ⟨⟨a, za⟩, ⟨b, zb⟩⟩ => ⟨⟨a, b⟩, za, zb⟩

end VG.Proof.Rsa.X86.InvBatchRt.Time

end

end

/-! ### `Rsa.X86.InvBatchRt.Time.Comp`, which this module and modules that import it used -/

section

/-! # The batched inverse's compound operations in both runs

Each is its parts' lemmas joined by `RelCT.seq`, given the analysis's check of each part (`Ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt

/-- The analysis checks `c` from `τS`. -/
def Ok (L : Lay) (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check sseTaint (τS L) c hc).isSome = true

variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

/-- What the operations need of the lengths: the sixteen arrays fit, and `n` is at least 2. -/
structure Room (Z len : Nat) : Prop where
  fit : 160 + 16 * (8 * nw len + 8) ≤ Z
  two : 2 ≤ nw len

/-- What the batches need of the lengths: `Room`, and `n` even and small enough to count its
batches and doublings in a word. -/
structure Fits (Z len : Nat) : Prop extends Room Z len where
  even : nw len % 2 = 0
  small : nw len ≤ 1024

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

theorem relCorrection {c i : Nat} (F : Room Z len) (hc4 : c + 4 ≤ 160) (hi : i < 11)
    (h₁ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₂ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf c))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (correction L c (a 11) (a i) tmp)
      (Both L B Z len N (nw len) args sp C T2) := by
  have F1 := F.fit
  have r11 := rv_a len 11 (nw len); have ri := rv_a len i (nw len); have r12 := rv_a len 12 (nw len)
  have e4 := rv_byte (kw len) (a 11) 4 (nw len)
  have rt : rv (kw len) tmp (nw len) = rv (kw len) (a 12) (nw len) := rfl
  have hiS : i * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
  exact RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
      (by simp only [Nat.add_zero]; omega_using [F1, r12, rt]) (by simp only [Nat.add_zero]; omega_using [F1, r11, e4]) (by simp only [Nat.add_zero]; omega_using [F1, ri, hiS])
      (by simp only [Nat.add_zero]; omega_using [r11, r12, e4, rt]) (by simp only [Nat.add_zero]; omega_using [ri, r12, rt, hiS]) h₁)
    (relMaskOfSel (stable_true _) hc4 (by omega_using [F1, r11]) (by omega_using [F1, r12, rt]) (by omega_using [r11, r12, rt]) h₂)

theorem relLinear {u v i j e : Nat} (F : Room Z len) (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    (he : e ≤ 1) (hi : i < 11) (hj : j < 11)
    (h₁ : Ok L (rowAdd L true u (a 11) (a i) (nBytes .esi e)))
    (h₂ : Ok L (rowAdd L false v (a 11) (a j) (nBytes .esi e)))
    (h₃ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a i) (nBytes .edx 0)))
    (h₄ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf u))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0))))
    (h₅ : Ok L (chain L .sbb tmp { (a 11) with byte := (a 11).byte + 4 } (a j) (nBytes .edx 0)))
    (h₆ : Ok L (.seq (.block (VG.Impl.Weierstrass.X86.Inv.maskOf v))
      (selIn L { (a 11) with byte := (a 11).byte + 4 } tmp (nBytes .edi 0)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (linear L u v (a 11) (a i) (a j) tmp e)
      (Both L B Z len N (nw len) args sp C T2) := by
  have F1 := F.fit
  have F2 := F.two
  have r11 := rv_a len 11; have ri := rv_a len i; have rj := rv_a len j
  have hiS : i * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have hjS : j * (8 * nw len + 8) + (8 * nw len + 8) ≤ 11 * (8 * nw len + 8) :=
    by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂
  unfold linear linearUnsigned
  exact RelCT.seq (RelCT.seq
      (relRowAdd (stable_true _) hu (by omega_using [he]) rfl (by omega_using [he, F1, r11]) (by omega_using [he, F1, ri, hiS]) (by omega_using [he, r11, ri, hiS]) h₁)
      (relRowAdd (stable_true _) hv (by omega_using [he]) rfl (by omega_using [he, F1, r11]) (by omega_using [he, F1, rj, hjS]) (by omega_using [he, r11, rj, hjS]) h₂))
    (RelCT.seq (relCorrection F hu hi h₃ h₄) (relCorrection F hv hj h₅ h₆))

/-- `csub src o` with any register facts that it keeps (`esi`'s, in the doublings). -/
theorem relCsub {G : (Reg → BitVec 32) → Prop} {src o : Ref}
    (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G) (F : Room Z len) (hsh : src.half = 0) (hoh : o.half = 0)
    (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z) (hoz : rv (kw len) o + 4 * nw len ≤ Z)
    (hts : rv (kw len) tmp + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) tmp)
    (hos : o ≠ src → rv (kw len) o + 4 * nw len ≤ rv (kw len) src ∨ rv (kw len) src + 4 * nw len ≤ rv (kw len) o)
    (hot : rv (kw len) o + 4 * nw len ≤ rv (kw len) tmp ∨ rv (kw len) tmp + 4 * nw len ≤ rv (kw len) o)
    (h₁ : Ok L (chain L .sbb tmp src mo (nBytes .edx 0))) (h₂ : Ok L (.block (borrowMask L src)))
    (h₃ : Ok L (if o = src then selIn L o tmp (nBytes .edi 0)
      else .seq (.block (ptr L .ebp src .edx ++ ptr L .ebx tmp .edx ++ nBytes .edx 0 ++ ptr L .edi o .eax))
        (.seq select3LoopX (.block (restoreEdi L))))) :
    RelCT isa (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.csub L src o)
      (Both L B Z len N (nw len) args sp C fun g => G g ∧ True) := by
  have F1 := F.fit
  have r12 := rv_a len 12; have r2 := rv_a len 2
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rs := rv_ge (kw len) src
  -- The parts' statements at rows of `nw len` words, the same places.
  have qs : rv (kw len) src (nw len) = rv (kw len) src := rfl
  have qo : rv (kw len) o (nw len) = rv (kw len) o := rfl
  have qt : rv (kw len) tmp (nw len) = rv (kw len) tmp := rfl
  have qm : rv (kw len) mo (nw len) = rv (kw len) mo := rfl
  obtain ⟨_, h₁⟩ := h₁; obtain ⟨_, h₂⟩ := h₂; obtain ⟨_, h₃⟩ := h₃
  unfold VG.Impl.Rsa.X86.InvBatchRt.csub
  refine RelCT.seq (relChainSub (X := Mask) hG (fun _ h => h) (by decide) rfl
      (by simp only [Nat.add_zero]; omega_using [F1, r12, rt, qt]) (by simp only [Nat.add_zero]; omega_using [hsz, qs]) (by simp only [Nat.add_zero]; omega_using [F1, r2, rmo, qm])
      (by simp only [Nat.add_zero]; omega_using [hts, qs, qt]) (by simp only [Nat.add_zero]; omega_using [r12, r2, rt, rmo, qt, qm]) h₁)
    (RelCT.seq (relBorrowMask (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hsh hsz h₂) ?_)
  by_cases ho : o = src
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ho)] at h₃ ⊢
    subst ho
    exact relSelIn (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) (by decide)
      (by simpa using hoz) (by simpa using (by omega_using [F1, r12, rt] : rv (kw len) tmp + 4 * nw len ≤ Z)) (by simp only [Nat.add_zero]; omega_using [hot, qo, qt]) h₃
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ho)] at h₃ ⊢
    exact relSelect3 (fun g g' k hg => hG g g' (fun r hr => k r (by simp_all)) hg) hoh hoz (by omega_using [hsz]) (by omega_using [F1, r12, rt])
      (hos ho) hot h₃

end VG.Proof.Rsa.X86.InvBatchRt.Time

end

end

/-! # The fused batches' operations in both runs

Each is `relOp` or `leafU` of its correctness, as the batched inverse's other operations
(`Kinds`), but the rows (`relRow`); a batch's rows keep the masks they read (`ME`), which
`coefMasks` and `mdme` write. `relBatchCodeF`: a batch, given the analysis's checks of its parts.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Weierstrass (Unch)
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt.F (maskW startF startF_ok coefMasks_ok mdme_ok batchCodeF scatter_ok gather_ok
  eOne_ok countF_ok RowWr de0 mul_step)
open VG.Impl.Rsa.X86.Keys (seqs)

/-- The terms of a batch from byte `i` of the elements. -/
def tU (i : Nat) : Term := ⟨i, win + 12, sMu⟩
def tV (i : Nat) : Term := ⟨i + 4, win + 16, sMu + 4⟩
def tQ (i : Nat) : Term := ⟨i, win + 20, sMu + 8⟩
def tR (i : Nat) : Term := ⟨i + 4, win + 24, sMu + 12⟩
def tD : Term := ⟨16, sMd + 8, sMm⟩
def tE : Term := ⟨16, sMd + 12, sMm + 4⟩

/-- The masks of the matrix, then those of `md`, `me` too. -/
def ms4 (i : Nat) : List Term := [tU i, tV i, tQ i, tR i]
def ms6 (i : Nat) : List Term := ms4 i ++ [tD, tE]

variable {L : Lay} {B : Addr} {Z len N n : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

/-- The runs between operations that keep the masks `ms`. -/
abbrev BM (L : Lay) (B : Addr) (Z len N n : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (C : Nat → Prop)
    (ms : List Term) (s t : State) : Prop :=
  Pre L B Z len N n args sp (ME B C ms) s ∧ Pre L B Z len N n args sp (ME B C ms) t

theorem relStartF {i : Nat} (hi : i + 8 ≤ fgSz) (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z)
    (h : Ok L (.block (startF L i))) :
    RelCT isa (Both L B Z len N n args sp C T2) (.block (startF L i)) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (ws := [(win + 4, 24)]) (by decide) (stable_true _) (fun w hw => by
      simp only [List.mem_singleton] at hw; subst w; exact ⟨.inr (by decide), by simp only [win]; omega_using [hfit]⟩)
    (fun s hb _ => WP.mono (startF_ok hb hi) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relCoefMasks {i : Nat} (h : Ok L (.block coefMasks)) :
    RelCT isa (Both L B Z len N n args sp C T2) (.block coefMasks) (BM L B Z len N n args sp C (ms4 i)) := by
  obtain ⟨_, h⟩ := h
  refine leafU (fun s ps => WP.mono (coefMasks_ok ps.1) fun u ⟨H, M, O, K⟩ => ?_) h
  have hn := ps.1.nowrap
  have hZ := ps.1.halfZ
  have hf := ps.1.fits16
  have eM : sMu = 160 := rfl; have e16 : win = 16 := rfl
  have co : ∀ j < 4, u.mem.readW (off B (win + 12 + 4 * j)) 32 = s.mem.readW (off B (win + 12 + 4 * j)) 32 :=
    fun j hj => BitVec.eq_of_toNat_eq (O.w32 (.inl (by omega_using [eM, e16, hj])) (by omega_using [e16, hj]))
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega_using [hf, eM])), ?_, fun t ht => ?_⟩
  · rw [O.w32 (.inl (by omega_using [eM])) (by omega_using [])]; exact ps.2.2.1
  · simp only [ms4, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · have := M 0 (by decide); have := co 0 (by decide); simp_all [tU]
    · have := M 1 (by decide); have := co 1 (by decide); simp_all [tV]
    · have := M 2 (by decide); have := co 2 (by decide); simp_all [tQ]
    · have := M 3 (by decide); have := co 3 (by decide); simp_all [tR]

theorem relMdme {i : Nat} (hi : i + 8 ≤ deSz) (h : Ok L (.block (mdme L i))) :
    RelCT isa (BM L B Z len N (nw len) args sp C (ms4 i)) (.block (mdme L i))
      (BM L B Z len N (nw len) args sp C (ms6 i)) := by
  obtain ⟨_, h⟩ := h
  refine leafU (fun s ps => WP.mono (mdme_ok ps.1 hi) fun u ⟨H, O, K, D⟩ => ?_) h
  have hn := ps.1.nowrap
  have hf := ps.1.fits16
  have eD : sMd = 184 := rfl; have eM : sMm = 200 := rfl; have eU : sMu = 160 := rfl; have e16 : win = 16 := rfl
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega_using [hf, eD])), ?_, fun t ht => ?_⟩
  · rw [O.w32 (.inl (by omega_using [eD])) (by omega_using [])]; exact ps.2.2.1
  · simp only [ms6, ms4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    have keep4 : ∀ t ∈ ms4 i, u.mem.readW (off B t.m) 32 = maskW (u.mem.readW (off B t.c) 32) := by
      intro t ht
      have ht' := ps.2.2.2 t ht
      simp only [ms4, List.mem_cons, List.not_mem_nil, or_false] at ht
      have hc : t.c + 4 ≤ sMu + 16 ∧ t.m + 4 ≤ sMu + 16 := by
        rcases ht with rfl | rfl | rfl | rfl <;> simp only [tU, tV, tQ, tR, win, sMu] <;> omega_using []
      rw [BitVec.eq_of_toNat_eq (O.w32 (d := t.m) (.inl (by omega_using [eD, eU, hc])) (by omega_using [eU, hc])),
        BitVec.eq_of_toNat_eq (O.w32 (d := t.c) (.inl (by omega_using [eD, eU, hc])) (by omega_using [eU, hc]))]
      exact ht'
    rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact keep4 _ (by simp [ms4])
    · exact D.mmd
    · exact D.mme

/-- A row writes its elements and the header's scratch words. -/
theorem RowWr.unch {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz) :
    Unch B [(A0, sz * (n + 2)), (sP, 8)] m m' := fun x hx => by
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  refine h x (fun j hj => ?_) h2
  have := mul_step (sz := sz) hj
  dsimp only at h1; omega_using [ho, h1, this]

theorem relScatter {arr sz x : Nat} {src : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (hA : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hsrc : rv (kw len) src n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) src n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) src n)
    (h : Ok L (scatter L arr sz x src)) :
    RelCT isa (Both L B Z len N n args sp C T2) (scatter L arr sz x src) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (ws := [(rv (kw len) { arr := arr } n, sz * (n + 2)), (sP, 8)]) (by decide) (stable_true _)
    (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> simp only [sP] at * <;> omega_using [hfit, hA])
    (fun s hb _ => WP.mono (scatter_ok hb hx hfit hA hsrc sep) fun _ ⟨H, R, _, K⟩ => ⟨H, K, RowWr.unch R hx, trivial⟩) h

theorem relGather {arr sz x : Nat} {dst : Ref} (hx : x + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z)
    (hdst : rv (kw len) dst n + 4 * (n + 1) ≤ Z)
    (sep : rv (kw len) dst n + 4 * (n + 1) ≤ rv (kw len) { arr := arr } n + sz ∨
      rv (kw len) { arr := arr } n + sz + sz * (n + 1) ≤ rv (kw len) dst n)
    (h : Ok L (gather L arr sz x dst)) :
    RelCT isa (Both L B Z len N n args sp C T2) (gather L arr sz x dst) (Both L B Z len N n args sp C T2) := by
  obtain ⟨_, h⟩ := h
  exact relOp (by decide) (stable_true _) (ws1 (by have := rv_ge (kw len) dst n; omega_using [this]) hdst)
    (fun s hb _ => WP.mono (gather_ok hb hx hfit hdst sep) fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

/-- `e = 1`. -/
theorem relEOne (hfit : 160 + 16 * (8 * nw len + 8) ≤ Z)
    (h : Ok L (.block (ptr L .eax { arr := deArr, byte := deSz } .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx]))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2)
      (.block (ptr L .eax { arr := deArr, byte := deSz } .edx ++ [.mov .ecx (.imm 1), .store (at_ .eax 4) .ecx]))
      (Both L B Z len N (nw len) args sp C T2) := by
  obtain ⟨_, h⟩ := h
  have ke := kw_eq len
  have r11 : de0 len = 160 + 11 * (4 * kw len + 8) + 20 := by simp only [de0, rv_arr]; rfl
  exact relOp (ws := [(de0 len + 4, 4)]) (by decide) (stable_true _) (ws1 (by omega_using [r11]) (by omega_using [hfit, ke, r11]))
    (fun s hb _ => WP.mono (eOne_ok hb) fun t ⟨H, M, K⟩ => ⟨H, K, by
      rw [M]; exact (writeW32_outside _ _ _ (by have := hb.nowrap; omega_using [hfit, ke, r11, this])).unch, trivial⟩) h

/-- The count of double batches, `(3 n + 2) / 2`. -/
theorem relCountF (F : Fits Z len)
    (h : Ok L (.block (nBytes .eax 0 ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
      .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax] : List Instr)))) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2)
      (.block (nBytes .eax 0 ++ ([.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
        .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 2), .shift .shr .eax 1, .store (sc 100) .eax] : List Instr)))
      (Both L B Z len N (nw len) args sp (· = (3 * nw len + 2) / 2) T2) := by
  obtain ⟨_, h⟩ := h
  have F4 := F.small
  refine leafU (fun s ps => WP.mono (countF_ok ps.1) fun t ⟨H, M, K⟩ => ?_) h
  have hn := ps.1.nowrap
  have hf := ps.1.fits16
  have O : Outside B 100 4 s.mem t.mem := by rw [M]; exact writeW32_outside _ _ _ (by omega_using [])
  refine ⟨H, ps.2.1.keep K (by decide) (O.mono (Nat.zero_le _) (by omega_using [hf])), ?_, trivial,
    trivial⟩
  show w32 t.mem B 100 = (3 * nw len + 2) / 2
  rw [M, w32_write_self, BitVec.toNat_ofNat]
  omega_using [F4]

/-! ## A batch -/

/-- The analysis's checks of a batch's parts. -/
structure BatchChecks (L : Lay) (i o : Nat) : Prop where
  start : Ok L (.block (startF L i))
  steps : Ok L (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)
  masks : Ok L (.block coefMasks)
  r₁ : RowChecks L false fgArr fgSz o [tU i, tV i] [tU i, tV i]
  r₂ : RowChecks L false fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i]
  mdme : Ok L (.block (mdme L i))
  r₃ : RowChecks L true deArr deSz o [tU i, tV i, tD] [tU i, tV i]
  r₄ : RowChecks L true deArr deSz (o + 4) [tQ i, tR i, tE] [tQ i, tR i]

theorem relBatchCodeF (F : Fits Z len) {i o : Nat} (hio : i = 0 ∧ o = 8 ∨ i = 8 ∧ o = 0) (K : BatchChecks L i o) :
    RelCT isa (Both L B Z len N (nw len) args sp C T2) (batchCodeF L i o)
      (Both L B Z len N (nw len) args sp C T2) := by
  have F1 := F.fit; have F2 := F.two; have he := F.even
  have r4 : rv (kw len) { arr := fgArr } (nw len) = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have r11 : rv (kw len) { arr := deArr } (nw len) = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have hi : i ≤ 8 := by omega_using [hio]
  have ho : o ≤ 8 := by omega_using [hio]
  have eP : sP = 176 := rfl; have eU : sMu = 160 := rfl; have eD : sMd = 184 := rfl; have eM : sMm = 200 := rfl
  have e16 : win = 16 := rfl; have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  have f2 : fgSz * (nw len + 2) = 16 * (nw len + 2) := rfl
  have d2 : deSz * (nw len + 2) = 20 * (nw len + 2) := rfl
  -- The rows' places.
  have hm4 : ∀ (arr : Nat), 208 ≤ rv (kw len) { arr := arr } (nw len) → ∀ t ∈ ms6 i,
      t.c + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧ t.m + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧
      (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m) := by
    intro arr ha t ht
    simp only [ms6, ms4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl | rfl | rfl) | (rfl | rfl) <;> simp only [tU, tV, tQ, tR, tD, tE] <;> omega_arith
  have hm4' : ∀ (arr : Nat), 208 ≤ rv (kw len) { arr := arr } (nw len) → ∀ t ∈ ms4 i,
      t.c + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧ t.m + 4 ≤ rv (kw len) { arr := arr } (nw len) ∧
      (t.c + 4 ≤ sP ∨ sP + 8 ≤ t.c) ∧ (t.m + 4 ≤ sP ∨ sP + 8 ≤ t.m) :=
    fun arr ha t ht => hm4 arr ha t (List.mem_append_left _ ht)
  have m4 : ∀ t ∈ ms4 i, t ∈ ms6 i := fun t ht => List.mem_append_left _ ht
  have H₁ : RowHyp len Z (nw len) fgArr fgSz o [tU i, tV i] [tU i, tV i] (ms4 i) :=
    ⟨F2, he, .inl rfl, by omega_using [hio, efs], by omega_using [F1, r4, f2], by omega_using [r4, eP], hm4' _ (by omega_using [F2, r4]), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tU, tV]; omega_using [hio, efs]⟩, fun _ h => h⟩
  have H₂ : RowHyp len Z (nw len) fgArr fgSz (o + 4) [tQ i, tR i] [tQ i, tR i] (ms4 i) :=
    ⟨F2, he, .inl rfl, by omega_using [hio, efs], by omega_using [F1, r4, f2], by omega_using [r4, eP], hm4' _ (by omega_using [F2, r4]), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact ⟨by simp [ms4], by simp only [tQ, tR]; omega_using [hio, efs]⟩, fun _ h => h⟩
  have H₃ : RowHyp len Z (nw len) deArr deSz o [tU i, tV i, tD] [tU i, tV i] (ms6 i) :=
    ⟨F2, he, .inr rfl, by omega_using [hio, eds], by omega_using [F1, F2, r11, d2], by omega_using [r11, eP], hm4 _ (by omega_using [r11]), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> exact ⟨by simp [ms6, ms4], by simp only [tU, tV, tD]; omega_arith⟩,
      fun t ht => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
        rcases ht with rfl | rfl <;> simp⟩
  have H₄ : RowHyp len Z (nw len) deArr deSz (o + 4) [tQ i, tR i, tE] [tQ i, tR i] (ms6 i) :=
    ⟨F2, he, .inr rfl, by omega_using [hio, eds], by omega_using [F1, F2, r11, d2], by omega_using [r11, eP], hm4 _ (by omega_using [r11]), fun t ht => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> exact ⟨by simp [ms6, ms4], by simp only [tQ, tR, tE]; omega_arith⟩,
      fun t ht => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
        rcases ht with rfl | rfl <;> simp⟩
  have toBoth : ∀ {ms : List Term} s t, BM L B Z len N (nw len) args sp C ms s t →
      Both L B Z len N (nw len) args sp C T2 s t :=
    fun _ _ ⟨ps, pt⟩ => ⟨⟨ps.1, ps.2.1, ps.2.2.1, trivial, trivial⟩, ⟨pt.1, pt.2.1, pt.2.2.1, trivial, trivial⟩⟩
  have mono4 : ∀ s t, BM L B Z len N (nw len) args sp C (ms6 i) s t →
      BM L B Z len N (nw len) args sp C (ms6 i) s t := fun _ _ h => h
  unfold batchCodeF
  simp only [seqs]
  refine RelCT.seq (relStartF (by omega_using [hio, efs]) F1 K.start) ?_
  refine RelCT.seq (relWordSteps (stable_true _) F1 (K.steps.choose_spec)) ?_
  refine RelCT.seq (relCoefMasks (i := i) K.masks) ?_
  refine RelCT.seq (relRow H₁ K.r₁) ?_
  refine RelCT.seq (relRow H₂ K.r₂) ?_
  refine RelCT.seq (relMdme (by omega_using [hio, eds]) K.mdme) ?_
  refine RelCT.seq (relRow H₃ K.r₃) ?_
  exact (relRow H₄ K.r₄).mono (fun _ _ h => mono4 _ _ h) toBoth

end VG.Proof.Rsa.X86.InvBatchRt.Time
