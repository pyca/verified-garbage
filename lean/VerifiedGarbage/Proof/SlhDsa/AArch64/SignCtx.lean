module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignTop
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: what holds in the body

From the entry state `σ` (`scratch = S = x7`, `sig = x6`): `Ctx` holds once
the body's first block has saved the caller's registers at `oTop`, written
the formatted message's header at `oHdr` and copied the four keys to
`oKeys`: the permissions and `sp`, `x19 = S`, the callee-saved registers no
code writes, the saved registers, the header and the keys, and that memory
changed only in `scratch`, `sig` and the 16 bytes below `sp`. Writes in
`scratch` outside `prot` (`oTop` to `oDigest`), in `sig` or below `sp` keep
it (`Ctx.of_frame`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Shake (topSaved)

/-- The callee-saved registers the functions never write. -/
abbrev untouched : List Reg := [.x26, .x27, .x28]

/-- `scratch`, `sig` and `sk` of the entry state `σ`. -/
abbrev scrOf (σ : State) : Addr := σ.gpr .x7
abbrev SCR (σ : State) : Region := ⟨σ.gpr .x7, scratchLen⟩
abbrev SIG (p : Params) (σ : State) : Region := ⟨σ.gpr .x6, p.sigLen⟩

/-- The private key and the randomness of the entry state `σ`. -/
abbrev skB (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) p.skLen
abbrev rndB (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x5) p.n

/-- The part of `scratch` `Ctx` keeps: the saved registers, the header and the keys. -/
abbrev PROT (σ : State) : Region := ⟨at' (σ.gpr .x7) Layout.oTop, 256⟩

/-- In the body, after its first block. -/
structure Ctx (p : Params) (σ t : State) : Prop where
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  sp : t.sp = σ.sp
  x19 : t.gpr .x19 = σ.gpr .x7
  cs : ∀ r ∈ untouched, t.gpr r = σ.gpr r
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  saved : ∀ i < 8, t.mem.readW (at' (σ.gpr .x7) (Layout.oTop + 8 * i)) 64 = σ.gpr (topSaved.getD i .x19)
  hdr : bytesAt t.mem (at' (σ.gpr .x7) Layout.oHdr) 2 = [0, BitVec.ofNat 8 (σ.gpr .x4).toNat]
  keys : ∀ c < 4, bytesAt t.mem (at' (σ.gpr .x7) (Layout.oKeys + 32 * c)) p.n =
    bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * c)) p.n
  frame : Frame [SCR σ, SIG p σ, below σ.sp 16] σ.mem t.mem

/-- A region the body may write without breaking `Ctx`. -/
def Free (p : Params) (σ : State) (r : Region) : Prop :=
  (Region.Sub r (SCR σ) ∧ r.Disjoint (PROT σ)) ∨ Region.Sub r (SIG p σ) ∨ Region.Sub r (below σ.sp 16)

theorem frame_free {p : Params} {σ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (h : ∀ r ∈ rs, Free p σ r) : Frame [SCR σ, SIG p σ, below σ.sp 16] m m' :=
  hf.sub fun r hr => by
    rcases h r hr with ⟨h1, -⟩ | h1 | h1
    · exact ⟨_, List.mem_cons_self .., h1⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h1⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h1⟩

/-- Bytes of `PROT` are kept by writes in free regions. -/
theorem prot_keep {p : Params} {σ : State} (hK : SG p σ) {rs : List Region}
    (h : ∀ r ∈ rs, Free p σ r) {a : Addr} {n : Nat} (ha : Region.Sub ⟨a, n⟩ (PROT σ)) :
    ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r := fun r hr => by
  rcases h r hr with ⟨-, h1⟩ | h1 | h1
  · exact (h1.symm.sub_left ha)
  · exact (hK.sig_scr.symm.sub_left (fun x hx => Offset.sub_base _ (by simp only [scratchLen]; decide) x (ha x hx))).sub_right h1
  · exact (hK.stk_scr.symm.sub_left (fun x hx => Offset.sub_base _ (by simp only [scratchLen]; decide) x (ha x hx))).sub_right h1

theorem prot_sub (σ : State) {o l : Nat} (h₁ : Layout.oTop ≤ o) (h₂ : o + l ≤ Layout.oTop + 256) :
    Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (PROT σ) := Offset.sub _ h₁ h₂

theorem Ctx.of_frame {p : Params} (hn : p.n ≤ 32) {σ t t' : State} (hK : SG p σ) (hc : Ctx p σ t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (h19 : t'.gpr .x19 = t.gpr .x19)
    (hcs : ∀ r ∈ untouched, t'.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    {rs : List Region} (hf : Frame rs t.mem t'.mem) (hfr : ∀ r ∈ rs, Free p σ r) : Ctx p σ t' := by
  have eT : Layout.oTop = 1536 := rfl
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, h19.trans hc.x19,
    fun r hr => (hcs r hr).trans (hc.cs r hr), fun r hr => (hv r hr).trans (hc.vcs r hr), fun i hi => ?_, ?_,
    fun c hc' => ?_, hc.frame.trans (frame_free hf hfr)⟩
  · rw [hf.readW (r := ⟨at' (σ.gpr .x7) (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
      (prot_keep hK hfr (prot_sub σ (by omega) (by omega))) (by decide)]
    exact hc.saved i hi
  · rw [bytesAt_frame hf (prot_keep hK hfr (prot_sub σ (by simp only [Layout.oHdr]; omega)
      (by simp only [Layout.oHdr]; omega))) (by decide)]
    exact hc.hdr
  · rw [bytesAt_frame hf (prot_keep hK hfr (prot_sub σ (by simp only [Layout.oKeys]; omega)
      (by simp only [Layout.oKeys]; omega))) (by omega)]
    exact hc.keys c hc'

end VG.Proof.SlhDsa.AArch64.Sign
