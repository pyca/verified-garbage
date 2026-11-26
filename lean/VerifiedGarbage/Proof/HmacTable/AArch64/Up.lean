module

public import VerifiedGarbage.Proof.HmacTable.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.TableFill
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# Tables of the interface `Hmac` on AArch64: what a caller's cleanup needs

What the cleanup of a function that calls HMAC's functions through a table of
`Hmac` needs of each variant's (`AArch64.Scrub.tabCallee`, with 16 bytes of
stack), which the kernel evaluates once for every variant (`variants_up`),
for every function that takes the tables.
-/

@[expose] public section

namespace VG.Proof.HmacTable.AArch64

open VG.AArch64 VG.AArch64.Scrub
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)
open VG.Proof.Variants.MdHash.AArch64 (variants)

/-- What the cleanup of a caller through a table needs of the HMAC functions of `w`. -/
def HmacUp (w : MdHash) : Prop :=
  tabCallee w.H.hmacInitAny 1 = true ∧ tabCallee w.H.updC 1 = true ∧ tabCallee w.H.hmacFin 1 = true

/-- `HmacUp` of every variant, evaluated once. -/
theorem variants_hmacUp : (variants.all fun w =>
    tabCallee w.H.hmacInitAny 1 && tabCallee w.H.updC 1 && tabCallee w.H.hmacFin 1) = true := by
  kernel_rfl

theorem variants_up : ∀ w ∈ variants, HmacUp w := fun w hw => by
  have h := List.all_eq_true.mp variants_hmacUp w hw
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A stub in the place of each of HMAC's functions. -/
def stubFns : Fns := ⟨[("t", tableStub 1)], [("t", tableStub 1)], [("t", tableStub 1)]⟩

theorem fnsOf_up {vs : List MdHash} (hv : ∀ w ∈ vs, HmacUp w) :
    (∀ q ∈ (fnsOf vs).init, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).upd, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) ∧
      (∀ q ∈ (fnsOf vs).fin, tabCallee q.2 1 = true ∧ q.1 ∈ names vs) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro q hq <;> obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
  · exact ⟨(hv w hw).1, (mem_names hw).1⟩
  · exact ⟨(hv w hw).2.1, (mem_names hw).2.1⟩
  · exact ⟨(hv w hw).2.2, (mem_names hw).2.2⟩

theorem mem_tableFns {vs : List MdHash} {f : String} (h : f ∈ names vs) :
    f ∈ tableFns [("hmac", tables vs)] := by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap]
  simp only [names, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := h
  exact ⟨t, ht, hf⟩

end VG.Proof.HmacTable.AArch64
