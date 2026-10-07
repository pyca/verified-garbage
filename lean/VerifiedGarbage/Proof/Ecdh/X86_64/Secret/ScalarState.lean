import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Entry
import VerifiedGarbage.Proof.Weierstrass.Window5Secret

/-! The immutable peer table and conditional accumulator invariant of the secret scalar loop. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

def scalarLive (K : WinCfg) : List Nat := jacCoords K.R++tableLive K 16

def recoded (K : WinCfg) (k : Nat) : Nat := k+16*Window5.geom K.J

structure TableData (K : WinCfg) (C : Curve) (E : Nat → Fe C) (P : Point C) : Prop where
  zero : E K.zero=0
  table : ∀ a,1≤a → a≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K a
    InvJ C (E p.x) (E p.y) (E p.z) (mul a P)
  cache : ∀ a,1≤a → a≤16 → let p := Impl.Ecdh.X86_64.Window5.tablePt K a
    E (p.x+96)=E p.z*E p.z ∧ E (p.x+128)=E (p.x+96)*E p.z

theorem TableData.congr {K : WinCfg} {C : Curve} {E F : Nat → Fe C} {P : Point C}
    (h : TableData K C E P) (hv : ∀ x∈tableLive K 16,F x=E x) : TableData K C F P := by
  refine ⟨?_,?_,?_⟩
  · rw [hv _ (by simp [tableLive,winRo])]
    exact h.zero
  · intro a ha ha16
    have v0 := hv _ (tableLive_entry K ha ha16 (i:=0) (by decide))
    have v1 := hv _ (tableLive_entry K ha ha16 (i:=1) (by decide))
    have v2 := hv _ (tableLive_entry K ha ha16 (i:=2) (by decide))
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul] at v0 v1 v2
    dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    rw [v0,v1,v2]
    exact h.table a ha ha16
  · intro a ha ha16
    dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    rw [hv _ (tableLive_entry K ha ha16 (i:=2) (by decide)),
      hv _ (tableLive_entry K ha ha16 (i:=3) (by decide)),
      hv _ (tableLive_entry K ha ha16 (i:=4) (by decide))]
    exact h.cache a ha ha16

theorem SecretLay.table_not_local {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈tableLive K 16,x∉localWrites K := by
  intro x hx hw
  rcases List.mem_append.mp hx with hx|hx
  · exact hL.ro x hx hw
  · have hl := hL.tbl x (List.mem_append_right _ hw)
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    omega

theorem TableData.keep {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {V V' : List Nat} {E F : Nat → Fe C} {P : Point C} {s t : State}
    (hL : SecretLay K size) (hs : Inv K.M base size C.p (·∈slots K) V E s)
    (ht : Inv K.M base size C.p (·∈slots K) V' F t)
    (hV : ∀ x∈tableLive K 16,x∈V) (hV' : ∀ x∈tableLive K 16,x∈V')
    (hk : CounterKeep K.M base (localWrites K) s t) (hd : TableData K C E P) :
    TableData K C F P :=
  hd.congr fun x hx => hk.field_eq hL.lay hs ht (local_slots K)
    (hV x hx) (hV' x hx) (hL.table_not_local x hx)

theorem SecretLay.entry_apart_r {K : WinCfg} {size : Nat} (hL : SecretLay K size) :
    ∀ x∈jacCoords K.R,x∉entryWrites K := by
  have hh := hL.nodup
  simp only [localWrites,winOther,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
  rw [hL.exy,hL.exz] at hh
  intro x hx hw
  simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases List.mem_append.mp hw with hw|hw
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    omega
  · have he := List.mem_singleton.mp hw
    grind

structure ScalarInv (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat)
    (P : Point C) (s₀ s : State) (j : Nat) : Prop where
  field : Inv K.M base size C.p (·∈slots K) (scalarLive K) (tmv C K.M.n base s) s
  data : TableData K C (tmv C K.M.n base s) P
  bits : ScalarBits K base (recoded K k) s
  counter : s.gpr .rbx=BitVec.ofNat 64 j
  acc : k<C.n → InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul (Window5.winE (recoded K k) K.J j) P)
  keep : CounterKeep K.M base (writes K) s₀ s

theorem scalarLive_zero (K : WinCfg) : K.zero∈scalarLive K := by simp [scalarLive,tableLive,winRo]

theorem scalarLive_table (K : WinCfg) : ∀ x∈tableSlots K 16,x∈scalarLive K :=
  fun _ hx => List.mem_append_right _ (List.mem_append_right _ hx)

theorem scalarLive_ro (K : WinCfg) : ∀ x∈tableLive K 16,x∈scalarLive K :=
  fun _ hx => List.mem_append_right _ hx

theorem entry_reads (K : WinCfg) {size : Nat} (hL : SecretLay K size) :
    ∀ x∈rcbR K.S K.R K.E++[K.E.x+96,K.E.x+128],x∈entryWrites K++scalarLive K := by
  intro x hx
  have vs : ∀ i<5,K.E.x+32*i∈consecutiveFields K.E.x 5 :=
    fun i hi => List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have v0 := vs 0 (by decide)
  have v1 := vs 1 (by decide)
  have v2 := vs 2 (by decide)
  have v3 := vs 3 (by decide)
  have v4 := vs 4 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,←hL.exy,←hL.exz] at v0 v1 v2 v3 v4
  simp only [rcbR,entryWrites,scalarLive,tableLive,winRo,jacCoords,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

end VG.Proof.Ecdh.X86_64.Secret
