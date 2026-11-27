module

public import VerifiedGarbage.Proof.Framework.AArch64.SideFill
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The cleanup of generic code that calls an implementation indirectly (AArch64)

`SideFill.lean` for code that calls the implementation it is generic over
by its address (`Code.icalls`, one candidate): built with that function's
body empty, the indirect calls of it are holes too, and the code for an
implementation is the closed code with its holes filled (`Code.fillCallsI`,
which fills both kinds). `sideAllI` is `Scrub.sideAll` but for those holes,
which it admits; the functions the code calls indirectly are then the
implementation alone, whose address the contract makes public (`hsy`), as
the cleanup needs (`noResidue_scrubAll`).
-/

@[expose] public section

namespace VG

/-- `c` with each call, direct or indirect, whose body is empty (a hole)
made a call of `n`, with body `b`, in the bodies of the functions `c` calls
too. -/
def Code.fillCallsI {M : ISA} (n : String) (b : Prog M) : Prog M → Prog M
  | .block is => .block is
  | .seq x y => .seq (fillCallsI n b x) (fillCallsI n b y)
  | .ite cd t e => .ite cd (fillCallsI n b t) (fillCallsI n b e)
  | .loop x cd => .loop (fillCallsI n b x) cd
  | .call m body => match body with
    | .block [] => .call n b
    | _ => .call m (fillCallsI n b body)
  | .frame i x j => .frame i (fillCallsI n b x) j
  | .icall i m x y => match x with
    | .block [] => .icall i n b (fillCallsI n b y)
    | _ => .icall i m x (fillCallsI n b y)

theorem Code.aarch64Depth_fillCallsI_le (n : String) (b e : Prog AArch64.isa) :
    (Code.fillCallsI n b e).aarch64Depth ≤ e.aarch64Depth + b.aarch64Depth := by
  induction e with
  | block is => exact Nat.zero_le _
  | seq x y ihx ihy =>
    simp only [Code.fillCallsI, Code.aarch64Depth]
    omega_using [ihx, ihy]
  | ite cd t e iht ihe =>
    simp only [Code.fillCallsI, Code.aarch64Depth]
    omega_using [iht, ihe]
  | loop x cd ih => simpa only [Code.fillCallsI, Code.aarch64Depth] using ih
  | call m body ih =>
    cases body with
    | block is =>
      cases is with
      | nil => exact Nat.le_add_left _ _
      | cons i is => exact Nat.le_add_right _ _
    | _ => simpa only [Code.fillCallsI, Code.aarch64Depth] using ih
  | frame i x j ih =>
    simp only [Code.fillCallsI, Code.aarch64Depth]
    omega_using [ih]
  | icall i m x y ihx ihy =>
    cases x with
    | block is =>
      cases is with
      | nil =>
        simp only [Code.fillCallsI, Code.aarch64Depth] at ihy ⊢
        omega_using [ihy]
      | cons i' is =>
        simp only [Code.fillCallsI, Code.aarch64Depth] at ihy ⊢
        omega_using [ihy]
    | _ =>
      simp only [Code.fillCallsI, Code.aarch64Depth] at ihx ihy ⊢
      omega_using [ihy]

namespace AArch64.Scrub

open VG.Impl.Scrub.AArch64

/-- `sideAll`, admitting indirect calls whose body is a hole. Only the
kernel evaluates it. -/
noncomputable def sideAllI (p : Instr → Bool) : Prog isa → Bool
  | .block is => Code.allInstrs p (.block is : Prog isa)
  | .seq a b => sideAllI p a && sideAllI p b
  | .ite _ t e => sideAllI p t && sideAllI p e
  | .loop b _ => sideAllI p b
  | .call _ b => sideAllI p b
  | .frame i b j => p i && sideAllI p b && p j
  | .icall i _ x y => p i && (match x with | .block [] => true | _ => false) && sideAllI p y

/-- What the cleanup needs of the closed code `e` with its holes filled by
`b`: every instruction meets `p`, and the functions it calls indirectly are
`n`. -/
theorem fillCallsI_ok {p : Instr → Bool} {n : String} {b e : Prog isa} (hb : sideAll p b = true)
    (he : sideAllI p e = true) :
    (Code.fillCallsI n b e).allInstrs p = true ∧ ∀ m ∈ inames (Code.fillCallsI n b e), m = n := by
  have hb' := allInstrs_of_sideAll hb
  have hbn : inames b = [] := inames_of_noIcall (noIcall_of_sideAll hb)
  induction e with
  | block is => exact ⟨he, fun _ h => by simp [Code.fillCallsI, inames] at h⟩
  | seq x y ihx ihy =>
    simp only [sideAllI, Bool.and_eq_true] at he
    obtain ⟨ax, nx⟩ := ihx he.1
    obtain ⟨ay, ny⟩ := ihy he.2
    refine ⟨by simp only [Code.fillCallsI, Code.allInstrs, ax, ay, Bool.and_self], fun m hm => ?_⟩
    simp only [Code.fillCallsI, inames, List.mem_append] at hm
    exact hm.elim (nx m) (ny m)
  | ite cd t f iht ihf =>
    simp only [sideAllI, Bool.and_eq_true] at he
    obtain ⟨at', nt⟩ := iht he.1
    obtain ⟨af, nf⟩ := ihf he.2
    refine ⟨by simp only [Code.fillCallsI, Code.allInstrs, at', af, Bool.and_self], fun m hm => ?_⟩
    simp only [Code.fillCallsI, inames, List.mem_append] at hm
    exact hm.elim (nt m) (nf m)
  | loop x cd ih =>
    simp only [sideAllI] at he
    obtain ⟨a, nm⟩ := ih he
    exact ⟨by simpa only [Code.fillCallsI, Code.allInstrs] using a,
      fun m hm => nm m (by simpa only [Code.fillCallsI, inames] using hm)⟩
  | call m' body ih =>
    simp only [sideAllI] at he
    cases body with
    | block is =>
      cases is with
      | nil => exact ⟨hb', fun m hm => by simp [Code.fillCallsI, inames, hbn] at hm⟩
      | cons i is =>
        obtain ⟨a, nm⟩ := ih he
        exact ⟨a, fun m hm => nm m hm⟩
    | _ =>
      obtain ⟨a, nm⟩ := ih he
      exact ⟨a, fun m hm => nm m hm⟩
  | frame i x j ih =>
    simp only [sideAllI, Bool.and_eq_true] at he
    obtain ⟨a, nm⟩ := ih he.1.2
    exact ⟨by simp only [Code.fillCallsI, Code.allInstrs, he.1.1, he.2, a, Bool.and_self],
      fun m hm => nm m (by simpa only [Code.fillCallsI, inames] using hm)⟩
  | icall i m' x y ihx ihy =>
    simp only [sideAllI, Bool.and_eq_true] at he
    obtain ⟨⟨hi, hx⟩, hy⟩ := he
    obtain ⟨ay, ny⟩ := ihy hy
    cases x with
    | block is =>
      cases is with
      | nil =>
        refine ⟨by simp only [Code.fillCallsI, Code.allInstrs, hi, hb', ay, Bool.and_self], fun m hm => ?_⟩
        simp only [Code.fillCallsI, inames, hbn, List.mem_append, List.mem_singleton] at hm
        exact hm.elim id (ny m)
      | cons _ _ => simp at hx
    | _ => simp at hx

/-- `verifiedScrubbedOfFill` for code whose holes are direct or indirect
calls of the implementation `n`, whose address the contract makes public
(`hsy`). -/
theorem verifiedScrubbedOfFillI {c e b : Prog isa} {n : String} {k : Contract isa} {W rb : Nat}
    (hv : Verified target c k) (hok : ScrubAllOk k W rb) (hc : c = Code.fillCallsI n b e)
    (hb : sideAll (fun i => !i.writesDit) b = true) (hbd : b.aarch64Depth = 0)
    (he : sideAllI (fun i => !i.writesDit) e = true) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hd : 16 * e.aarch64Depth ≤ W) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64)
    (hsy : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.syms n = s₂.syms n) :
    VerifiedScrubbed target (scrubOf W rb c) k rb := by
  obtain ⟨ha, hn⟩ := fillCallsI_ok (n := n) hb he
  have hdc : 16 * c.aarch64Depth ≤ W := by
    have := Code.aarch64Depth_fillCallsI_le n b e
    rw [hc]
    omega_using [hbd, hd, this]
  subst hc
  exact ⟨Verified.scrubAll (Clear.of_wf _) hv hW hrb hok,
    noResidue_scrubAll (Clear.of_wf _) (Clear.of_keeps _) hv hW hok.sp hdc (Code.all_of_allInstrs ha)
      (fun s₁ s₂ hp m hm => by rw [hn m hm]; exact hsy s₁ s₂ hp) hrb, fun ty _ h => by cases ty <;> cases h⟩

end AArch64.Scrub

end VG
