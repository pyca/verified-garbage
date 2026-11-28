module

-- separate module: the parse and FORS stages of verify's correctness, which the layers' stage builds on; one module of the chain of verify's proof, each a stage

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopFors
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsBase
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect
import VerifiedGarbage.Proof.SlhDsa.X86_64.WotsBlocks
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4AvxCorrect

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the body of its frame

Untrusted: everything here is checked by Lean. From the digest: the indices,
layer 0's addresses and `forsPk` (`fors_ok`); the layers' loop (`loop_ok`);
the comparison with `PK.root` and the result (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)
open VG.Impl.SlhDsa.X86_64.Shake (oKgSave treeLanes stk)
open VG.Impl.SlhDsa.X86_64.Verify (vvar vParseIdx fVSig forsPk xmssPk)
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem vars_lanes {L : VL} {i : Nat} (hi : i < 4) : ∀ r ∈ [KeyGen.lanesR L.S], Region.Disjoint ⟨L.var i, 8⟩ r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Levels.disj_scr L.S (by simp only [Layout.oA, show oKgSave = 34080 from rfl]; omega)
    (by rw [show oKgSave = 34080 from rfl]; omega) (by simp only [Layout.oA]; omega)

theorem inFrS {t : State} (hc : Ctx L g m₀ t) {d : Nat} (h : d + 8 ≤ 72) :
    InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 d) 8 := by
  rw [hc.rsp]; exact hc.inFr h

theorem inVar {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : i < 4) : InRegions (t.rd ++ t.wr) (L.var i) 8 := by
  obtain ⟨r, hr, h⟩ := var_in hc hi
  exact ⟨r, List.mem_append_right _ hr, h⟩

/-- The digest's indices, as `splitDigest` gives them. -/
abbrev dTree (p : Params) (m : Mem) (S : Addr) : Nat := (splitDigest p (bytesAt m (at' S Layout.oDigest) p.m)).2.1
abbrev dLeaf (p : Params) (m : Mem) (S : Addr) : Nat := (splitDigest p (bytesAt m (at' S Layout.oDigest) p.m)).2.2

theorem dTree_lt {p : Params} (hp : VPar p) (m : Mem) (S : Addr) : dTree p m S < 2 ^ 64 := by
  have h := Nat.mod_lt (toInt ((bytesAt m (at' S Layout.oDigest) p.m |>.drop p.mdLen).take p.treeIdxLen) p.treeIdxLen)
    (Nat.pow_pos (n := p.h - p.h / p.d) (show 0 < 2 by decide))
  have := hp.tb; have := hp.tb'
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))

theorem dLeaf_lt {p : Params} (hp : VPar p) (m : Mem) (S : Addr) : dLeaf p m S < 2 ^ p.hp := by
  unfold dLeaf splitDigest
  rw [← hp.hd]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem digest_frame {p : Params} (hp : VPar p) {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {S : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' S Layout.oDigest, p.m⟩ r) :
    bytesAt m' (at' S Layout.oDigest) p.m = bytesAt m (at' S Layout.oDigest) p.m :=
  bytesAt_frame hf hd (by have := hp.m64; omega)

theorem digest_vars {p : Params} (hp : VPar p) (S : Addr) :
    ∀ r ∈ [(⟨at' S (oKgSave + 48), 32⟩ : Region)], Region.Disjoint ⟨at' S Layout.oDigest, p.m⟩ r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  have := hp.m64
  exact Levels.disj_scr S (by simp only [show Layout.oDigest = 30304 from rfl, show oKgSave = 34080 from rfl]; omega)
    (by simp only [show Layout.oDigest = 30304 from rfl]; omega) (by rw [show oKgSave = 34080 from rfl]; omega)

theorem digest_lanes {p : Params} (hp : VPar p) (S : Addr) :
    ∀ r ∈ [KeyGen.lanesR S], Region.Disjoint ⟨at' S Layout.oDigest, p.m⟩ r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  have := hp.m64
  exact Levels.disj_scr S (by simp only [show Layout.oDigest = 30304 from rfl, Layout.oA]; omega)
    (by simp only [show Layout.oDigest = 30304 from rfl]; omega) (by simp only [Layout.oA]; omega)

theorem mdAt_eq {p : Params} (hp : VPar p) (m : Mem) (S : Addr) :
    mdAt p m S = (splitDigest p (bytesAt m (at' S Layout.oDigest) p.m)).1 := by
  simp only [mdAt, splitDigest]
  rw [bytesAt_take' _ _ (by have := hp.m; omega)]

/-- At the call of `forsPk`, from the state `t₀` after the digest. -/
structure B2Post (p : Params) (L : VL) (g : Reg → BitVec 64) (m₀ : Mem) (t₀ t : State) : Prop where
  ctx : Ctx L g m₀ t
  adr : Adr L t.mem (Proof.SlhDsa.layerTree 0 (dTree p t₀.mem L.S))
  rdi : t.gpr .rdi = L.S
  rsi : t.gpr .rsi = L.sig + BitVec.ofNat 64 p.n
  rdx : t.gpr .rdx = BitVec.ofNat 64 (dLeaf p t₀.mem L.S)
  v0 : t.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (dTree p t₀.mem L.S)
  v1 : t.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (dLeaf p t₀.mem L.S)
  dg : bytesAt t.mem (at' L.S Layout.oDigest) p.m = bytesAt t₀.mem (at' L.S Layout.oDigest) p.m

/-- The indices, layer 0's addresses, and `forsPk`'s arguments. -/
theorem b2_ok {p : Params} (hp : VPar p) (hL : L.Ok) (hn : L.n = p.n) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (vParseIdx p ++ ([.mov32 .r10 (.imm 0), .mov .r9 (.mem (vvar 0))] : List Instr) ++
        treeLanes p .r10 .r9 ++ ([.mov .rdi (.reg .rbx), .mov .rsi (.mem (stk fVSig)),
          .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)), .mov .rdx (.mem (vvar 1))] : List Instr))) t
      (B2Post p L g m₀ t) := by
  have hn32 := hL.n32
  have hTl := dTree_lt hp t.mem L.S
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (parse_ok hp hL hc) fun t₁ ⟨hc₁, v0, v1, f₁⟩ => ?_)
  refine wp_mov32i fun t₂ u₂ => wp_movm (a := L.var 0) (by rw [ea_vvar, u₂.other _ (by decide), hc₁.rbx])
    (by rw [u₂.rd, u₂.wr]; exact inVar hc₁ (by omega)) fun t₃ u₃ => ?_
  have hc₃ : Ctx L g m₀ t₃ := (hc₁.regs u₂.rd u₂.wr u₂.mem fun r hr => u₂.other r (by
    intro e; subst e; revert hr; decide)).regs u₃.rd u₃.wr u₃.mem fun r hr => u₃.other r (by
    intro e; subst e; revert hr; decide)
  refine WP.block_append (M := isa) (l₁ := treeLanes p .r10 .r9) ?_
  refine (lanes_ok hL hn (j := 0) (T := dTree p t.mem L.S) (by decide) hTl hc₃
    (by rw [u₃.other _ (by decide), u₂.gpr]; rfl) (by rw [u₃.gpr, u₂.mem, v0]) fun u hcu hgu had hfu => ?_)
  refine wp_mov fun t₄ u₄ => wp_movm (a := L.SP + BitVec.ofNat 64 16) (by
      rw [show stk fVSig = stk 16 from rfl, ea_stk, u₄.other _ (by decide), hcu.rsp])
    (by rw [u₄.rd, u₄.wr]; exact hcu.inFr (by omega)) fun t₅ u₅ => wp_addi fun t₆ u₆ =>
    wp_movm (a := L.var 1) (by rw [ea_vvar, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      hcu.rbx]) (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact inVar hcu (by omega)) fun t₇ u₇ =>
    WP.block_nil ?_
  have hm₇ : t₇.mem = u.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have hvu : ∀ i < 4, u.mem.readW (L.var i) 64 = t₁.mem.readW (L.var i) 64 := fun i hi => by
    rw [Thash4Avx.readW_frame hfu (vars_lanes hi), u₃.mem, u₂.mem]
  refine ⟨hcu.regs (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr]) hm₇
    fun r hr => by
      have h1 : r ≠ .rdx := by intro e; subst e; revert hr; decide
      have h2 : r ≠ .rsi := by intro e; subst e; revert hr; decide
      have h3 : r ≠ .rdi := by intro e; subst e; revert hr; decide
      rw [u₇.other _ h1, u₆.other _ h2, u₅.other _ h2, u₄.other _ h3], by rw [hm₇]; exact had,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hcu.rbx],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.mem, hcu.pSig, Levels.sx_ofNat (by omega)],
    by rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, hvu 1 (by omega), v1],
    by rw [hm₇, hvu 0 (by omega), v0], by rw [hm₇, hvu 1 (by omega), v1], ?_⟩
  rw [hm₇, digest_frame hp hfu (digest_lanes hp L.S), u₃.mem, u₂.mem, digest_frame hp f₁ (digest_vars hp L.S)]

/-- From the digest: the indices, layer 0's addresses, and `forsPk`. -/
theorem fors_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hp : VPar p) (hmx : (forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true) (hsp : NoSp (forsPk p f))
    (hst : T.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n) (hsl : p.n + p.forsSigLen ≤ L.sigL) (name : String)
    {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (vParseIdx p ++ ([.mov32 .r10 (.imm 0), .mov .r9 (.mem (vvar 0))] : List Instr) ++
        treeLanes p .r10 .r9 ++ ([.mov .rdi (.reg .rbx), .mov .rsi (.mem (stk fVSig)),
          .alu .add .rsi (.imm (BitVec.ofNat 32 p.n)), .mov .rdx (.mem (vvar 1))] : List Instr)))
      (.call name (forsPk p f))) t fun t' => Ctx L g m₀ t' ∧
        t'.mem.readW (L.var 0) 64 = BitVec.ofNat 64 (dTree p t.mem L.S) ∧
        t'.mem.readW (L.var 1) 64 = BitVec.ofNat 64 (dLeaf p t.mem L.S) ∧
        bytesAt t'.mem (at' L.S Layout.oMsg) p.n = forsPkFromSig p (bytesAt m₀ (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen)
          (splitDigest p (bytesAt t.mem (at' L.S Layout.oDigest) p.m)).1 (bytesAt m₀ L.pk L.n)
          (forsAdrs (Proof.SlhDsa.layerTree 0 (dTree p t.mem L.S)) (dLeaf p t.mem L.S)) := by
  have hLl := dLeaf_lt hp t.mem L.S
  have hhp := hp.hp9
  refine WP.seq (WP.mono (b2_ok hp hL hn hc) fun t₇ hb => ?_)
  refine WP.mono (forsCall_ok T ht hp hmx hsp hst hL hn hsl hb.ctx hb.adr
    (Nat.lt_of_lt_of_le hLl (Nat.pow_le_pow_right (by decide) (by omega))) hb.rdi hb.rsi hb.rdx name)
    fun t' ⟨hc', hv', hmsg⟩ => ⟨hc', ?_, ?_, ?_⟩
  · rw [hv' 0 (by omega), hb.v0]
  · rw [hv' 1 (by omega), hb.v1]
  · rw [hmsg, mdAt_eq hp, hb.dg]

end VG.Proof.SlhDsa.X86_64.VerifyTop
