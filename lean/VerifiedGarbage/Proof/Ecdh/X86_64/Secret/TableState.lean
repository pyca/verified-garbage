import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Layout
import VerifiedGarbage.Proof.Weierstrass.X86_64.CounterKeep

/-! The initialized table prefix, valid field values, cached powers and public counter. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

def tableLive (K : WinCfg) (m : Nat) : List Nat := winRo K++tableSlots K m

/-- Validation supplies a curve point even for rejected inputs, selecting the
standard generator when peer validation fails. -/
structure TableInv (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (s₀ s : State) (m : Nat) : Prop where
  field : Inv K.M base size C.p (·∈slots K) (tableLive K m) (tmv C K.M.n base s) s
  peer : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
    (tmv C K.M.n base s K.P.z) P
  affine : tmv C K.M.n base s K.P.z=1
  table : ∀ a,1≤a → a≤m →
    let p := Impl.Ecdh.X86_64.Window5.tablePt K a
    InvJ C (tmv C K.M.n base s p.x) (tmv C K.M.n base s p.y) (tmv C K.M.n base s p.z) (mul a P)
  cache : ∀ a,1≤a → a≤m →
    let p := Impl.Ecdh.X86_64.Window5.tablePt K a
    tmv C K.M.n base s (p.x+96)=tmv C K.M.n base s p.z*tmv C K.M.n base s p.z ∧
    tmv C K.M.n base s (p.x+128)=tmv C K.M.n base s (p.x+96)*tmv C K.M.n base s p.z
  counter : s.gpr .rbx=BitVec.ofNat 64 (m+1)
  keep : CounterKeep K.M base (writes K) s₀ s

theorem tableLive_read (K : WinCfg) (m : Nat) :
    ∀ x∈rcbR K.S K.R K.P,x∈jacCoords K.R++tableLive K m := by
  intro x hx
  simp only [rcbR,jacCoords,tableLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem tableLive_slots (K : WinCfg) {m : Nat} (hm : m≤16) :
    ∀ x∈tableLive K m,x∈slots K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ (List.mem_append_left _ hx)
  · exact List.mem_append_right _ (table_slots_mono K hm x hx)

theorem tableLive_entry (K : WinCfg) {m a i : Nat}
    (ha : 1≤a) (ham : a≤m) (hi : i<5) : K.tbl+160*(a-1)+32*i∈tableLive K m :=
  List.mem_append_right _ (table_mem K ha ham hi)

theorem tableLive_next (K : WinCfg) (m : Nat) :
    ∀ x∈tableLive K (m+1),x∈consecutiveFields (K.tbl+160*m) 5++tableLive K m := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_right _ (List.mem_append_left _ hx)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases ho : i<5*m
    · exact List.mem_append_right _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i,List.mem_range.mpr ho,rfl⟩))
    · exact List.mem_append_left _ (List.mem_map.mpr
        ⟨i-5*m,List.mem_range.mpr (by omega),by omega⟩)

end VG.Proof.Ecdh.X86_64.Secret
