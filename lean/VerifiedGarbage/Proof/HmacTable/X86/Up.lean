module

public import VerifiedGarbage.Proof.HmacTable.X86
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Framework.X86.TableFill
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Tables of the interface `Hmac` on x86: what a caller's cleanup needs

What the cleanup of a function that calls HMAC's functions through a table of
`Hmac` needs of each variant's (`X86.Scrub.calleeSide`, with the stack every
variant's uses at most), which the kernel evaluates once for every variant (`vs_up`), for
every function that takes the tables.
-/

@[expose] public section

namespace VG.Proof.HmacTable.X86

open VG.X86 VG.X86.Scrub

/-- The HMAC implementations of the registrations' tables. -/
abbrev vs : List HVar :=
  vars VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants

/-- What the cleanup of a caller through a table needs of the HMAC functions of `w`. -/
def HmacUp (w : HVar) : Prop :=
  calleeSide w.F.hmacInitAny 76 = true ∧ calleeSide w.F.H.updC 20 = true ∧ calleeSide w.F.hfC 48 = true

/-- `HmacUp` of every variant, evaluated once. -/
theorem vs_hmacUp : (vs.all fun w =>
    calleeSide w.F.hmacInitAny 76 && calleeSide w.F.H.updC 20 && calleeSide w.F.hfC 48) = true := by
  kernel_rfl

theorem vs_up : ∀ w ∈ vs, HmacUp w := fun w hw => by
  have h := List.all_eq_true.mp vs_hmacUp w hw
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A stub in the place of each of HMAC's functions. -/
def stubFns : Impl.Ecdsa.Rfc6979.X86.Fns := ⟨[("t", tableStub 76)], [("t", tableStub 20)], [("t", tableStub 48)]⟩

theorem fnsOf_up {vs : List HVar} (hv : ∀ w ∈ vs, HmacUp w) :
    (∀ q ∈ (fnsOf vs).init, calleeSide q.2 76 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).upd, calleeSide q.2 20 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).fin, calleeSide q.2 48 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  · exact ⟨(hv w hw).1, (mem_names hw).1⟩
  · exact ⟨(hv w hw).2.1, (mem_names hw).2.1⟩
  · exact ⟨(hv w hw).2.2, (mem_names hw).2.2⟩

theorem mem_tableFns {vs : List HVar} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hmac", tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
  simp only [names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact ⟨t, ht, hf⟩

end VG.Proof.HmacTable.X86
