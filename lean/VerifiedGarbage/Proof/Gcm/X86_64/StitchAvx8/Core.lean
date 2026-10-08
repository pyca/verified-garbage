import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.DataInv
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Prepare

/-! # Data and hash positions shared by the encrypt and decrypt loops -/

namespace VG.Proof.Gcm.X86_64.StitchAvx8
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block ghashFrom)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)

def hashBlock (s₀ : State) (dec : Bool) (k : Nat) : Block := if dec then blk s₀ k else ctb s₀ k

def hashPrefix (s₀ : State) (dec : Bool) (g : Nat) : Block :=
  ghashFrom (hk s₀) (y₀ s₀) ((List.range g).map (hashBlock s₀ dec))

def HashLaw (s₀ : State) (P : Nat → Block) : Prop := ∀ X y,
  reduceB (accN X P y 8) = ghashFrom (hk s₀) y ((List.range 8).map X)

theorem ghash_append8 (h y : Block) (f : Nat → Block) (g : Nat) :
    ghashFrom h y ((List.range (g + 8)).map f) =
      ghashFrom h (ghashFrom h y ((List.range g).map f)) ((List.range 8).map fun i => f (g + i)) := by
  rw [List.range_add, List.map_append, List.map_map]
  simp only [ghashFrom, List.foldl_append]
  rfl

structure CoreInv (s₀ : State) (P : Nat → Block) (dec : Bool) (c g : Nat) (s : State) : Prop where
  env : Env s₀ P s
  data : DataInv s₀ c s.mem
  templates : Templates s₀ c 0 s.mem
  counter : (s.gpr .r8).setWidth 32 = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 (c + 8)
  cursor : s.gpr .rdx = bAddr s₀ g
  remaining : s.gpr .r9 = BitVec.ofNat 64 (nb s₀ - g)
  hash : s.lane .xmm2 0 = hashPrefix s₀ dec g
  c_le : c ≤ nb s₀
  g_le : g ≤ nb s₀

theorem CoreInv.initial {s₀ s : State} {P : Nat → Block} (hp : SPre s₀)
    (h : Ready s₀ P s) (dec : Bool) : CoreInv s₀ P dec 0 0 s := by
  refine ⟨h.env, DataInv.initial hp h, h.templates, h.counter, ?_, ?_, ?_, Nat.zero_le _, Nat.zero_le _⟩
  · simpa only [bAddr, Nat.mul_zero, BitVec.add_zero] using h.cursor
  · simpa only [Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.remaining
  · exact h.hash

theorem CoreInv.addr {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (h : CoreInv s₀ P dec c g s) (k : Nat) :
    s.gpr .rdx + BitVec.ofNat 64 (16 * k) = bAddr s₀ (g + k) := by rw [h.cursor, bAddr_add]

theorem CoreInv.batchBounds {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (j : Nat) (hj : g + j = c) (hc : c + 8 ≤ nb s₀) :
    (∀ k < 8, InRegions s₀.wr (s.gpr .rdx + BitVec.ofNat 64 (16 * (j + k))) 16) ∧
    (s.gpr .rdx).toNat + 16 * (j + 8) ≤ 2 ^ 64 ∧ Region.Sub (batchR s j) (dR s₀) := by
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [h.addr, ← Nat.add_assoc, hj]
    exact in_sub hp.d_in (by omega)
  · rw [h.cursor, bAddr_toNat hp g (by omega)]
    have hw := hp.wrap_d
    omega
  · change Region.Sub ⟨s.gpr .rdx + BitVec.ofNat 64 (16 * j), 128⟩ (dR s₀)
    rw [h.addr, hj]
    exact Offset.sub_base (dp s₀) (d := 16 * c) (n := 128) (k := 16 * nb s₀) (by omega)

theorem CoreInv.bareBatch {s₀ s : State} {P : Nat → Block} {dec : Bool} {c g : Nat}
    (hp : SPre s₀) (h : CoreInv s₀ P dec c g s) (j : Nat) (hj : g + j = c) (hc : c + 8 ≤ nb s₀) :
    WP isa (Impl.Gcm.X86_64.StitchAvx8.batch (nr s₀) 8 j (fun _ => [])) s
      (CoreInv s₀ P dec (c + 8) g) := by
  let X : Nat → Block := fun i => s.mem.readW (hashAddr s₀ i) 128
  have hB : Prepared s₀ X X 0 s.mem := fun _ _ => rfl
  obtain ⟨hw, hwrap, hsub⟩ := h.batchBounds hp j hj hc
  refine WP.mono (batch_ok hp false false j h.env h.templates hB h.hash h.counter hw hwrap hsub
    (fun he => Bool.noConfusion he) (fun he => Bool.noConfusion he)
    (fun he => Bool.noConfusion he) (fun he => Bool.noConfusion he)) fun t ht => ?_
  refine ⟨ht.env, h.data.batch hp hc (by rw [h.addr, hj]) ht, ht.templates, ?_,
    (ht.regs _ (by decide) (by decide)).trans h.cursor,
    (ht.regs _ (by decide) (by decide)).trans h.remaining, ht.hash, hc, h.g_le⟩
  simpa only [Nat.add_assoc, Nat.reduceAdd] using ht.counter

end VG.Proof.Gcm.X86_64.StitchAvx8
