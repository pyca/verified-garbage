module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
public import VerifiedGarbage.Proof.MlKem.X86_64.FragDM

/-!
# ML-KEM on x86-64: the polynomial primitives, inline

The code of a polynomial primitive run inline in another function, with the
moves of its arguments before it (`glueIn_ok`): it leaves the permissions
and the callee-saved registers as they were, and changes memory only within
the buffers it writes (`IPost`). For each primitive the K-PKE functions run
inline, what it needs of the state (`…Hi`: as for a call, `FragPrim.lean`,
with the return address in place of the stack below it) and what it does
(`…In_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What inline code leaves: the permissions and the callee-saved registers,
and memory changed only within `W`. -/
structure IPost (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame W s.mem s'.mem

theorem IPost.rsp {s s' : State} {W : List Region} (h : IPost s s' W) : s'.gpr .rsp = s.gpr .rsp :=
  h.cs .rsp (by decide)

theorem IPost.pa {s s' : State} {W : List Region} (h : IPost s s' W) {p : Ptr} (hp : p.1 ∈ calleeSaved) :
    pa s' p = pa s p := by
  simp only [VG.Proof.MlKem.X86_64.pa, h.cs _ hp]

theorem IPost.trans {s₁ s₂ s₃ : State} {W : List Region} (h₁ : IPost s₁ s₂ W) (h₂ : IPost s₂ s₃ W) :
    IPost s₁ s₃ W :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), h₁.frame.trans h₂.frame⟩

theorem IPost.mono {s s' : State} {W W' : List Region} (h : IPost s s' W) (hs : ∀ r ∈ W, r ∈ W') :
    IPost s s' W' :=
  ⟨h.rd, h.wr, h.cs, h.frame.mono hs⟩

/-- The moves of the arguments, then verified code inline. -/
theorem glueIn_ok {glue : List Instr} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) {s : State} {V : State → Prop}
    (hg : WP isa (.block glue) s fun s1 => (V s1 ∧ s1.mem = s.mem) ∧ Keep argRegs s s1)
    {rd wr : List Region} (hpre : ∀ s1, V s1 → s1.mem = s.mem → Keep argRegs s s1 → k.pre (s1.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.seq (.block glue) c) s fun s' => IPost s s' wr ∧
      ∃ s1, V s1 ∧ s1.mem = s.mem ∧ Keep argRegs s s1 ∧ k.post (s1.withRegions rd wr) (s'.withRegions rd wr) := by
  refine WP.seq (WP.mono hg fun s1 ⟨⟨hV, hm⟩, k1⟩ => ?_)
  refine WP.inline hv (hpre s1 hV hm k1) (by rw [k1.2.1, k1.2.2]; exact hc) (by rw [k1.2.2]; exact hw)
    (fun s' hrd hwr habi hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [habi.1 r hr, k1.gpr (argRegs_cs r hr)], by rw [hm] at hf; exact hf⟩,
      s1, hV, hm, k1, hpost⟩) hn

/-- The return address is apart from a region, after moves that keep the stack pointer. -/
theorem retR_keep {s s1 : State} (k : Keep argRegs s s1) {R : Region} (h : (retR s).Disjoint R) (rd wr : List Region) :
    (retR (s1.withRegions rd wr)).Disjoint R := by
  simp only [retR, State.withRegions_gpr, k.gpr (r := .rsp) (by decide)]
  exact h

/-! ## `ByteDecode₁₂` -/

/-- What inline code reading `n` bytes at `p` and writing `m` at `q` needs. -/
structure TwoHi (p q : Ptr) (n m : Nat) (s : State) : Prop where
  off : p.2 < 2 ^ 31 ∧ q.2 < 2 ^ 31
  d : Region.Disjoint ⟨pa s p, n⟩ ⟨pa s q, m⟩
  rP : (retR s).Disjoint ⟨pa s p, n⟩
  rQ : (retR s).Disjoint ⟨pa s q, m⟩
  c : Covers ([⟨pa s p, n⟩] ++ [⟨pa s q, m⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s q, m⟩] s.wr

theorem dec12In_ok {c : Prog isa} (hv : ∀ s, decode12K.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧
      decode12K.post s s') (hn : c.noCalls = true) {p q : Ptr} (hq : NA q) {s : State} (h : TwoHi p q 384 1024 s) :
    WP isa (.seq (.block (lea .rdi p ++ lea .rsi q)) c) s fun s' => IPost s s' [pR (pa s q)] ∧
      PolyIs s'.mem (pa s q) (decode12 (bytesAt s.mem (pa s p) 384)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueIn_ok hv hn (accGlue_ok p q h.off.1 h.off.2 hq1 s) (rd := [⟨pa s p, 384⟩]) (wr := [pR (pa s q)])
    (fun s1 hv _ k => by
      simp only [decode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, hv.1, hv.2]
      exact ⟨trivial, trivial, h.d, retR_keep k h.rP _ _, retR_keep k h.rQ _ _⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [decode12K, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2, hm] at hq
  exact hq

/-! ## `vg_mlkem_add`, `vg_mlkem_sub` -/

/-- What inline code of `f ← t f g` needs. -/
structure AccHi (f g : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (pa s f)
  redG : Reduced s.mem (pa s g)
  d : (pR (pa s f)).Disjoint (pR (pa s g))
  rF : (retR s).Disjoint (pR (pa s f))
  rG : (retR s).Disjoint (pR (pa s g))
  c : Covers ([pR (pa s g)] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

theorem accIn_ok {t : Poly → Poly → Poly} {c : Prog isa}
    (hv : ∀ s, (accK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accK t).post s s')
    (hn : c.noCalls = true) {f g : Ptr} (hgr : g.1 ≠ .rdi) {s : State} (h : AccHi f g s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi g)) c) s fun s' =>
      IPost s s' [pR (pa s f)] ∧ PolyIs s'.mem (pa s f) (t (polyAt s.mem (pa s f)) (polyAt s.mem (pa s g))) := by
  refine WP.mono (glueIn_ok hv hn (accGlue_ok f g h.off.1 h.off.2 hgr s) (rd := [pR (pa s g)]) (wr := [pR (pa s f)])
    (fun s1 hv hm k => by
      simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        hv.1, hv.2, hm]
      exact ⟨trivial, trivial, h.d, retR_keep k h.rF _ _, retR_keep k h.rG _ _, h.redF, h.redG⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [accK, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2, hm] at hq
  exact hq

/-! ## `ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` -/

/-- What inline code compressing `f` to `out` with width `d` in `ws` needs. -/
structure CEHi (ws : List Nat) (f out : Ptr) (d : Nat) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31
  dw : d ∈ ws
  red : Reduced s.mem (pa s f)
  dj : Region.Disjoint (pR (pa s f)) ⟨pa s out, 32 * d⟩
  rF : (retR s).Disjoint (pR (pa s f))
  rO : (retR s).Disjoint ⟨pa s out, 32 * d⟩
  c : Covers ([pR (pa s f)] ++ [⟨pa s out, 32 * d⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s out, 32 * d⟩] s.wr

theorem ceIn_ok {n : String} {c : Prog isa} {ws : List Nat} (I : CEImpl n c ws) (hn : c.noCalls = true)
    {f out : Ptr} {d : Nat} (hout : NA out) {s : State} (h : CEHi ws f out d s) :
    WP isa (.seq (.block (lea .rdi f ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rdx out ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) c) s fun s' =>
      IPost s s' [⟨pa s out, 32 * d⟩] ∧
      bytesAt s'.mem (pa s out) (32 * d) = compressEncode d (polyAt s.mem (pa s f)) := by
  have hd := I.le d h.dw
  refine WP.mono (glueIn_ok I.correct hn (ceGlue_ok f out d h.off hd hout s) (rd := [pR (pa s f)])
    (wr := [⟨pa s out, 32 * d⟩])
    (fun s1 hv hm k => by
      simp only [compressEncodeWK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        State.withRegions_mem, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega),
        sw32_64' d (by omega), hm]
      exact ⟨trivial, trivial, h.dj, retR_keep k h.rF _ _, retR_keep k h.rO _ _, h.dw, trivial, h.red⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [compressEncodeWK, dArg, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega), hm] at hq
  exact hq

/-- What inline code decompressing the `32d` bytes at `b` to `f`, with `d` in `ws`, needs. -/
structure DDHi (ws : List Nat) (b f : Ptr) (d : Nat) (s : State) : Prop where
  off : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31
  dw : d ∈ ws
  dj : Region.Disjoint ⟨pa s b, 32 * d⟩ (pR (pa s f))
  rB : (retR s).Disjoint ⟨pa s b, 32 * d⟩
  rF : (retR s).Disjoint (pR (pa s f))
  c : Covers ([⟨pa s b, 32 * d⟩] ++ [pR (pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (pa s f)] s.wr

theorem ddIn_ok {n : String} {c : Prog isa} {ws : List Nat} (I : DDImpl n c ws) (hn : c.noCalls = true)
    {b f : Ptr} {d : Nat} (hf : NA f) {s : State} (h : DDHi ws b f d s) :
    WP isa (.seq (.block (lea .rdi b ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))),
      .mov32 .rdx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rcx f)) c) s fun s' =>
      IPost s s' [pR (pa s f)] ∧
      PolyIs s'.mem (pa s f) (decodeDecompress d (bytesAt s.mem (pa s b) (32 * d))) := by
  have hd := I.le d h.dw
  refine WP.mono (glueIn_ok I.correct hn (ddGlue_ok b f d h.off hd hf s) (rd := [⟨pa s b, 32 * d⟩])
    (wr := [pR (pa s f)])
    (fun s1 hv _ k => by
      simp only [decodeDecompressWK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega)]
      exact ⟨trivial, trivial, h.dj, retR_keep k h.rB _ _, retR_keep k h.rF _ _, h.dw, trivial⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [decodeDecompressWK, dArg, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), sw32_64' d (by omega), hm] at hq
  exact hq

/-! ## `vg_mlkem*_decrypt_mul` -/

/-- What inline code of `vg_mlkem*_decrypt_mul` of rank `k` needs. -/
structure DecMulHi (k : Nat) (w s u z : Ptr) (st : State) : Prop where
  off : w.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ u.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redS : VecReduced st.mem (pa st s) k
  redU : VecReduced st.mem (pa st u) k
  ws : (pR (pa st w)).Disjoint (vR (pa st s) k)
  wu : (pR (pa st w)).Disjoint (vR (pa st u) k)
  wz : (pR (pa st w)).Disjoint (cR (pa st z))
  sz : (vR (pa st s) k).Disjoint (cR (pa st z))
  uz : (vR (pa st u) k).Disjoint (cR (pa st z))
  rW : (retR st).Disjoint (pR (pa st w))
  rS : (retR st).Disjoint (vR (pa st s) k)
  rU : (retR st).Disjoint (vR (pa st u) k)
  rZ : (retR st).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st s) k, vR (pa st u) k] ++ [pR (pa st w), cR (pa st z)]) (st.rd ++ st.wr)
  wc : Covers [pR (pa st w), cR (pa st z)] st.wr

theorem decMulIn_ok {k : Nat} {c : Prog isa}
    (hv : ∀ s, (decMulK k).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (decMulK k).post s s')
    (hn : c.noCalls = true) {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z) {st : State}
    (H : DecMulHi k w s u z st) :
    WP isa (.seq (.block (lea .rdi w ++ lea .rsi s ++ lea .rdx u ++ lea .rcx z)) c) st fun s' =>
      IPost st s' [pR (pa st w), cR (pa st z)] ∧
      PolyIs s'.mem (pa st w) (nttInv (dot (vecAt st.mem (pa st s) k) ((vecAt st.mem (pa st u) k).map ntt))) := by
  refine WP.mono (glueIn_ok hv hn (dmGlue_ok w s u z H.off hs hu hz st) (rd := [vR (pa st s) k, vR (pa st u) k])
    (wr := [pR (pa st w), cR (pa st z)])
    (fun s1 hv hm k1 => by
      simp only [decMulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
        hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hm]
      exact ⟨trivial, trivial, H.ws, H.wu, H.wz, H.sz, H.uz, retR_keep k1 H.rW _ _, retR_keep k1 H.rS _ _,
        retR_keep k1 H.rU _ _, retR_keep k1 H.rZ _ _, H.redS, H.redU⟩) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [decMulK, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1, hm] at hq
  exact hq

end VG.Proof.MlKem.X86_64
