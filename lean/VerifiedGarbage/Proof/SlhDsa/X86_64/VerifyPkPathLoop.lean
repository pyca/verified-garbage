module

-- separate module: a stage of `xmssPk`'s proof, so that a change to a later stage does not rebuild it

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkPath
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA on x86-64, `xmssPk`: the authentication path

The loop of `pathBody` (`Impl/SlhDsa/X86_64/Verify.lean`) from height 0 to
`h′`: with the WOTS⁺ public key first in lane 0 of `A`'s message, it leaves
there the root the path gives (`path`, `Proof/SlhDsa/VerifySpec.lean`),
from the authentication path, the `h′·n` bytes after the WOTS⁺ signature at
`sig`, which is read only.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.SlhDsa

/-- String `z` of the `c` strings of `n` bytes at `a`. -/
theorem chunk_bytesAt (m : Mem) (a : Addr) {n z c : Nat} (hz : z < c) :
    chunk (bytesAt m a (c * n)) n z = bytesAt m (a + BitVec.ofNat 64 (z * n)) n := by
  have hl : (chunk (bytesAt m a (c * n)) n z).length = n := by
    simp only [chunk, List.length_take, List.length_drop, bytesAt, List.length_map, List.length_range]
    have : n ≤ c * n - n * z := by
      rw [Nat.mul_comm n z, ← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left n (by omega_using [hz])
    omega_using [this]
  apply List.ext_getElem (by rw [hl]; simp [bytesAt])
  intro i h₁ h₂
  have hi : i < n := by rw [hl] at h₁; exact h₁
  have hzn : n * z + i < c * n := by
    have : n * z + n ≤ c * n := by rw [Nat.mul_comm c n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left n hz
    omega_using [this, hi]
  simp only [chunk, List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_comm z n]

/-- Every region `changes` lists is in `scratch`. -/
theorem changes_sub_scr {p : Params} (hn : p.n ≤ 32) (S : Addr) :
    ∀ r ∈ changes p S, Region.Sub r ⟨S, 2 ^ 16⟩ := by
  have e : ∀ c, (Layout.laneA c = 3296 + 128 * c) ∧ Layout.laneB c = 3808 + 2208 * c := fun c => ⟨rfl, rfl⟩
  intro r hr
  simp only [changes, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨k', hk', rfl | rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  · exact Region.sub_prefix (by decide)
  · exact Offset.sub_base S (by decide)
  · exact Offset.sub_base S (by simp only [Layout.oVars]; omega)
  · rw [(e k').1]; exact Offset.sub_base S (by simp only [Layout.strideA]; omega)
  · rw [(e k').2]; exact Offset.sub_base S (by simp only [Layout.strideB]; omega)
  all_goals
    have e₁ : Layout.oN = 12640 := rfl
    have e₂ : Layout.oRoots = 29280 := rfl
    have e₃ : Layout.oDigits = 30368 := rfl
    have e₄ : Layout.oMsg = 30496 := rfl
    have e₅ : Layout.oFidx = 31328 := rfl
    have e₆ : Layout.nodeSlots = 520 := rfl
    exact Offset.sub_base S (by omega)

/-- The loop of `pathBody`, from height 0: the root the authentication path
gives, from the node first in lane 0 of `A`'s message. -/
theorem pathLoop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (hlen : p.len * p.n < 2 ^ 31)
    (hhp : 0 < p.hp) (hhp' : p.hp < 63) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {idx : Nat} {pkSeed a16 : List Byte} (hidx : idx < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 idx) (h13 : s.gpr .r13 = sig)
    (hv3 : s.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 0)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.xmssSigLen⟩ : Region) ∈ s.rd) (hsfit : sig.toNat + p.xmssSigLen ≤ 2 ^ 64)
    (hss : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hsb : Region.Disjoint ⟨sig, p.xmssSigLen⟩ (below (s.gpr .rsp) stack))
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n =
        path p pkSeed a16 2 0 idx (bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n)) (p.hp * p.n)) p.hp
          (bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n) →
      Frame (chFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (.loop (Impl.SlhDsa.X86_64.Verify.pathBody p f) .ne) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hxs : p.xmssSigLen = (p.len + p.hp) * p.n := rfl
  -- the signature's bytes stay as they were
  have hsigF : ∀ {m : Mem}, Frame (chFrame p S (s.gpr .rsp) stack) s.mem m →
      ∀ {o l : Nat}, o + l ≤ p.xmssSigLen →
        bytesAt m (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := by
    intro m hf o l hol
    have hsub : Region.Sub ⟨sig + BitVec.ofNat 64 o, l⟩ ⟨sig, p.xmssSigLen⟩ := Offset.sub_base sig hol
    exact bytesAt_frame hf (chFrame_disj' hn32 (hss.sub_left hsub) (hsb.sub_left hsub)) (by omega_using [hol, hsfit])
  let auth := bytesAt s.mem (sig + BitVec.ofNat 64 (p.len * p.n)) (p.hp * p.n)
  let node0 := bytesAt s.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n
  -- the invariant, at the start of height `z`
  let Inv : Nat → State → Prop := fun m t => ∃ z, m = p.hp - z ∧ z < p.hp ∧
    (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.gpr .rsp = s.gpr .rsp ∧
    t.mem.readW (at' S (Layout.oVar 1 3)) 64 = BitVec.ofNat 64 z ∧
    bytesAt t.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = path p pkSeed a16 2 0 idx auth z node0 ∧
    Frame (chFrame p S (s.gpr .rsp) stack) s.mem t.mem
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h12cs : Reg.r12 ∈ calleeSaved := by decide
  have h13cs : Reg.r13 ∈ calleeSaved := by decide
  refine WP.loop (M := isa) Inv (fun m t ⟨z, hm, hz, gt, rt, wt, spt, vt, lt, ft⟩ => ?_) (p.hp - 0) s
    ⟨0, rfl, hhp, fun _ _ => rfl, rfl, rfl, rfl, hv3, rfl, Frame.refl _ _⟩
  have henvt := Env.of_frame hn32 henv (ft.sub (chFrame_sub p S _ stack)) hstk
  have hzn : p.len * p.n + z * p.n + p.n ≤ p.xmssSigLen := by
    rw [hxs, Nat.add_mul, Nat.add_assoc, ← Nat.succ_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hz) _
  refine pathBody_ok T ht hn hfam hlen hhp' hst hs63 hidx hz (by rw [gt _ hbxcs, hbx]) (by rw [gt _ h12cs, h12])
    (by rw [gt _ h13cs, h13]) vt (by rw [wt]; exact hw) hS (by rw [spt]; exact hstk) henvt
    (fun j hj => ⟨_, List.mem_append_left _ (by rw [rt]; exact hsr), by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base sig (by omega_using [hzn, hj, hn]) (by omega_using [hzn, hsfit, hj, hn])⟩)
    (hss.sub_left (Offset.sub_base sig hzn)) fun t' g' r' w' v' z' l' f' => ?_
  have ft' : Frame (chFrame p S (s.gpr .rsp) stack) s.mem t'.mem := ft.trans (by rw [spt] at f'; exact f')
  have hsp' : t'.gpr .rsp = s.gpr .rsp := by rw [g' _ (by decide), spt]
  -- the path's node `z`, as the specification's chunk of it
  have hch : chunk auth p.n z = bytesAt t.mem (sig + BitVec.ofNat 64 (p.len * p.n + z * p.n)) p.n := by
    rw [chunk_bytesAt s.mem _ hz, BitVec.add_assoc, ← BitVec.ofNat_add, hsigF ft hzn]
  have hstep : bytesAt t'.mem (at' S (Layout.laneA 0 + p.n + 32)) p.n = path p pkSeed a16 2 0 idx auth (z + 1) node0 := by
    rw [l', path, ← lt, hch]
  by_cases hlast : z + 1 = p.hp
  · refine Or.inl ⟨by show t'.zf.map (!·) = some false; rw [z', decide_eq_true hlast]; rfl, ?_⟩
    exact k t' (fun r hr => by rw [g' r hr, gt r hr]) (by rw [r', rt]) (by rw [w', wt])
      (by rw [hstep, hlast]) ft'
  · refine Or.inr ⟨by show t'.zf.map (!·) = some true; rw [z', decide_eq_false hlast]; rfl, p.hp - (z + 1),
      by omega_using [hm, hz, hlast], z + 1, rfl, by omega_using [hz, hlast],
      fun r hr => by rw [g' r hr, gt r hr], by rw [r', rt], by rw [w', wt], hsp', v', hstep, ft'⟩

end VG.Proof.SlhDsa.X86_64
