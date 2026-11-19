module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
public import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim

/-! ### `MlKem.X86_64.InlinePrim`, which the modules that import this one used -/

section

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

/-- Code run from a state that permits more than its proof's state: the
code changes memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.narrowIn {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P) (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    (hn : c.noCalls = true) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      P (s'.withRegions rd wr) → Q s') : WP isa c s Q :=
  regionModel.wp_narrow h hc hw (Code.noFrames_of_noCalls hn) (.inl hn)
    fun _ _ he hr hw hf hp => hQ _ hr hw hf (fun _ h => Exec.gpr h he) hp

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
        State.withRegions_mem, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega_using [hd]),
        sw32_64' d (by omega_using [hd]), hm]
      exact ⟨trivial, trivial, h.dj, retR_keep k h.rF _ _, retR_keep k h.rO _ _, h.dw, trivial, h.red⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [compressEncodeWK, dArg, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega_using [hd]), sw32_64' d (by omega_using [hd]), hm] at hq
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
        hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega_using [hd]), sw32_64' d (by omega_using [hd])]
      exact ⟨trivial, trivial, h.dj, retR_keep k h.rB _ _, retR_keep k h.rF _ _, h.dw, trivial⟩) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, _, hq⟩ => ⟨hpost, ?_⟩
  simp only [decodeDecompressWK, dArg, State.withRegions_gpr, State.withRegions_mem, hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega_using [hd]), sw32_64' d (by omega_using [hd]), hm] at hq
  exact hq

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DcBase`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: decapsulation, its contract, layout, checks and entry

For a parameter set `L`: the contract the proof is written against
(`decapsK L`, which the shared contract implies), the layout of the
function's buffers (`dk` and `c` in `rbp` and `r14`, which may overlap each
other; `scratch` and `key` in `rbx` and `r12`), what holds throughout (`DC`:
`Top`, and `dk` and `c` at their pointers), the checks of the layout every
piece needs (`DcWf L`), and the prologue.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemDecaps L (dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def decapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.dkLen⟩, ⟨s.gpr .rsi, L.ctLen⟩] ∧ s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.dkLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => decapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.dkLen)
      (bytesAt s.mem (s.gpr .rsi) L.ctLen)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    dkRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.dkLen) = dkRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.dkLen)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev dcM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]
/-- `dk` and `c`. -/
abbrev dcR : List (Reg × Nat) := [(.rbp, L.dkLen), (.r14, L.ctLen)]
/-- `scratch` and `key`. -/
abbrev dcW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32)]
abbrev dcB : List (Reg × Nat) := dcR L ++ dcW L

theorem dcB_bases : ∀ b ∈ dcB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem dcM_bases : ∀ p ∈ dcM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `DC`. -/
def dcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (dcB L) ws && keepB (dcB L) ws (.rbp, 0) L.dkLen && keepB (dcB L) ws (.r14, 0) L.ctLen

/-- A piece that writes `ws` keeps `DR nu ns`. -/
def drChk (nu ns : Nat) (ws : List (Ptr × Nat)) : Bool :=
  dcChk L ws && (List.range nu).all (fun i => keepB (dcB L) ws (pS i) 1024) &&
    (List.range ns).all (fun i => keepB (dcB L) ws (pS (L.k + i)) 1024)

abbrev uW (i : Nat) : List (Ptr × Nat) := [(pS i, 1024)]

def uChk (i : Nat) : Bool :=
  twoChk (dcB L) (dcW L) (.r14, 32 * L.du * i) (32 * L.du) (pS i) 1024 && drChk L i 0 (uW i)

def sChk (i : Nat) : Bool :=
  twoChk (dcB L) (dcW L) (.rbp, 384 * i) 384 (pS (L.k + i)) 1024 && drChk L L.k i [(pS (L.k + i), 1024)]

/-- What `vg_mlkem*_decrypt_mul` writes: polynomial 15, and its working space. -/
abbrev dmW : List (Ptr × Nat) := [(pS 15, 1024), (pS (2 * L.k), 4096)]

abbrev tailW : List (Ptr × Nat) := dmW L ++ [(pS 16, 1024)] ++ [(pS 16, 1024)] ++ [(sc oM, 32 * 1)]

def tailChk : Bool :=
  dmChk (dcB L) (dcW L) L.k (pS 15) (pS L.k) (pS 0) (pS (2 * L.k)) &&
    twoChk (dcB L) (dcW L) (.r14, 32 * L.du * L.k) (32 * L.dv) (pS 16) 1024 &&
    keepB (dcB L) [(pS 16, 1024)] (pS 15) 1024 && accChk (dcB L) (dcW L) (pS 16) (pS 15) &&
    twoChk (dcB L) (dcW L) (pS 16) 1024 (sc oM) (32 * 1) && dcChk L (tailW L) && dcChk L (dmW L)

def dckChk (ws : List (Ptr × Nat)) : Bool := dcChk L ws && keepB (dcB L) ws (sc oG) 32 && keepB (dcB L) ws (sc oKB) 32

/-- The writes of the hashes. -/
abbrev hW₁ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]
abbrev hW₂ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oKB, 32)]

/-- What the pieces of decapsulation that do not depend on how it stores its
polynomials need of the layout (the hashes, the choice of the key, with `c'`
at `scratch + oc`, and the end), evaluated for each parameter set. -/
structure DcWfB (oc : Nat) : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ dcB L, b.2 < 2 ^ 32
  -- the hashes
  h₁ : hashChk (dcB L) (dcW L) [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)] 72 (sc oG) 64 = true
  h₁K : dcChk L hW₁ = true
  h₁M : keepB (dcB L) hW₁ (sc oM) 32 = true
  h₂ : hashChk (dcB L) (dcW L) [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)] 136 (sc oKB) 32 = true
  h₂K : dcChk L hW₂ = true
  h₂G : keepB (dcB L) hW₂ (sc oG) 64 = true
  h₂M : keepB (dcB L) hW₂ (sc oM) 32 = true
  -- the choice of the key
  selK : dcChk L [((.r12, 0), 32)] = true
  sel : inB (dcB L) (.r14, 0) L.ctLen = true ∧ inB (dcB L) (sc oc) L.ctLen = true ∧
    inB (dcB L) (sc oG) 32 = true ∧ inB (dcB L) (sc oKB) 32 = true ∧ inB (dcW L) (.r12, 0) 32 = true ∧
    sepB (dcB L) (sc oG) 32 (.r12, 0) 32 = true ∧ sepB (dcB L) (sc oKB) 32 (.r12, 0) 32 = true
  ct : oc < 2 ^ 31 ∧ L.ctLen < 2 ^ 32 ∧ 0 < L.ctLen ∧ L.ctLen % 8 = 0
  sv : ∀ k < 6, inB (dcB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (dcB L) (sc 0) 1 = true ∧ inB (dcB L) (.r12, 0) 1 = true ∧ inB (dcB L) (.r14, 0) 1 = true
  selT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r12, .r14]) (selectAt oc L.ctLen) h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 384 * L.k + 384 * L.k) 32)
    h).isSome = true

/-- What every piece of decapsulation with polynomials of `u32`s needs of the
layout, evaluated for each parameter set. -/
structure DcWf : Prop extends DcWfB L L.oCT where
  -- K-PKE.Decrypt
  u : ∀ i < L.k, uChk L i = true
  s : ∀ i < L.k, sChk L i = true
  tail : tailChk L = true
  enc : Enc.encChk L (dcB L) (dcW L) (dckChk L) (.rbp, 384 * L.k) = true

instance : CoeOut (DcWf L) (DcWfB L L.oCT) := ⟨DcWf.toDcWfB⟩

section
variable {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ)
include W hp

theorem dcLay {s : State} (h : Top dcM σ s) : Lay (dcR L) (dcW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r14 = σ.gpr .rsi := h.regs (.r14, .rsi) (by decide)
  have e4 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d4
  · exact fun _ => d3
  · exact fun _ => d5.symm
  exacts [k1, k2, k4, k3, n1, n2, n4, n3,
    mem ⟨σ.gpr .rdi, L.dkLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, L.ctLen⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rcx, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r2, r4, r3]

end

/-- `dk` and `c`. -/
abbrev dcDk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.dkLen
abbrev dcC (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) L.ctLen

/-- What holds throughout. -/
structure DC (L : Kem) (σ s : State) : Prop where
  top : Top dcM σ s
  dk : bytesAt s.mem (pa s (.rbp, 0)) L.dkLen = dcDk L σ
  c : bytesAt s.mem (pa s (.r14, 0)) L.ctLen = dcC L σ

section
variable {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ)
include W hp

theorem DC.lay {s : State} (h : DC L σ s) : Lay (dcR L) (dcW L) s := dcLay W hp h.top

theorem DC.step {s s' : State} (h : DC L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : dcChk L ws = true) : DC L σ s' := by
  simp only [dcChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP dcM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.dk,
    by rw [L₀.keepBytes hP hc.2]; exact h.c⟩

end

/-- Bytes of a buffer. -/
theorem slice_of {s : State} {r : Reg} {n : Nat} {B : List Byte} (h : bytesAt s.mem (pa s (r, 0)) n = B) {o l : Nat}
    (hol : o + l ≤ n) : bytesAt s.mem (pa s (r, o)) l = (B.drop o).take l := by
  rw [← h, bytesAt_slice _ _ hol, pa, pa, off_add, Nat.zero_add]

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r14 (.reg .rsi), .mov .r12 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) :
    WP isa (.block pro) σ fun s => DC L σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega_using [hsc])
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega_using [hsc]); have w1 := w 848 (by omega_using [hsc]); have w2 := w 856 (by omega_using [hsc])
  have w3 := w 864 (by omega_using [hsc]); have w4 := w 872 (by omega_using [hsc]); have w5 := w 880 (by omega_using [hsc])
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r14 = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h14, h12, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega_using [hsc]))).writeW (List.mem_singleton_self _) _ (c 856 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega_using [hsc]))).writeW (List.mem_singleton_self _) _ (c 872 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega_using [hsc])))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hdk := W.small (.rbp, L.dkLen) (by simp)
  have hct := W.small (.r14, L.ctLen) (by simp)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h14 h12, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by simp only at hdk; omega_using [n1])
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d4) (by simp only at hct; omega_using [n2])

end Decaps

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation, K-PKE.Decrypt

`u'[i]` (`u_ok`), `ŝ[i]` (`s_ok`), and `m' = ByteEncode₁(Compress₁(v' -
NTT⁻¹(ŝ^⊺ ∘ NTT(u'))))` to `M`, the product in one call of
`vg_mlkem*_decrypt_mul` (`tail_ok`): `m' = K-PKE.Decrypt(dk_PKE, c)`. Between
the steps, `DR nu ns`: the first `nu` of `u'` and `ns` of `ŝ` are done. Each
with its constant time.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (decapsK L).pre (decapsK L).pub I

theorem dc_lrel {L : Kem} {oc : Nat} (W : DcWfB L oc) {σ₁ σ₂ x y : State} (p₁ : (decapsK L).pre σ₁) (p₂ : (decapsK L).pre σ₂)
    (pub : (decapsK L).pub σ₁ σ₂) (h₁ : DC L σ₁ x) (h₂ : DC L σ₂ y) : LRel (dcR L) (dcW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r14, .rsi) (by decide), h₂.top.regs (.r14, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]

/-- The steps of K-PKE.Decrypt. -/
structure DR (L : Kem) (nu ns : Nat) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = 1
  u : ∀ i < nu, PolyIs s.mem (pa s (pS i)) (KPke.dcU L.p (dcC L σ) i)
  sh : ∀ i < ns, PolyIs s.mem (pa s (pS (L.k + i))) (dcS (KPke.dkPke L.p (dcDk L σ)) i)

theorem DR.keep {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {nu ns : Nat} {s s' : State}
    (h : DR L nu ns σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : drChk L nu ns ws = true) :
    DR L nu ns σ s' := by
  simp only [drChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hdc, kU⟩, kS⟩ := hc
  have L₀ := h.dc.lay W.toDcWfB hp
  exact ⟨h.dc.step W.toDcWfB hp hP.b hdc, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun i hi => L₀.keepPoly hP.b (kU i hi) (h.u i hi), fun i hi => L₀.keepPoly hP.b (kS i hi) (h.sh i hi)⟩

theorem DR.zero {L : Kem} {σ s : State} (h : DC L σ s) (h15 : s.gpr .r15 = 1) : DR L 0 0 σ s :=
  ⟨h, h15, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `32 d_u (i + 1) ≤ |c|`. -/
theorem uSlice_le (L : Kem) {i : Nat} (hi : i < L.k) : 32 * L.du * i + 32 * L.du ≤ L.ctLen := by
  have : 32 * L.du * (i + 1) ≤ 32 * L.du * L.k := Nat.mul_le_mul_left _ hi
  simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.k] at this ⊢
  rw [Nat.mul_succ] at this
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega_using [this]

/-! ## `u'` -/

theorem u_ok (A : Arith) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ : State}
    (hp : (decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State} (h : DR L i 0 σ s) :
    WP isa (uHat L A i) s (DR L (i + 1) 0 σ) := by
  have hc := W.u i hi
  simp only [uChk, Bool.and_eq_true] at hc
  obtain ⟨hdd, hrc⟩ := hc
  have L₀ := h.dc.lay W.toDcWfB hp
  unfold uHat
  refine WP.mono (ddCall_okL (K.dd A.codecs) L₀ (d := L.du) rbx_na hdd K.du.2) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  have hk := h.keep W hp hP₁ hrc
  refine ⟨hk.dc, hk.r15, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega_using [hk'] : k < i ∨ k = i) with hk' | rfl
  · exact hk.u k hk'
  · rw [← hP₁.pa rbx_cs, slice_of h.dc.c (uSlice_le L hi)] at hp₁
    exact hp₁

theorem u_tr (A : Arith) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {i : Nat}
    (hi : i < L.k) : RelCT isa (R L (DR L i 0)) (uHat L A i) fun _ _ => True := by
  have hc := W.u i hi
  simp only [uChk, Bool.and_eq_true] at hc
  exact rel2_of (ddCall_trL (K.dd A.codecs) (d := L.du) rbx_na hc.1 K.du.2)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W.toDcWfB p₁ p₂ pub h₁.dc h₂.dc

/-! ## `ŝ` -/

theorem s_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {σ : State} (hp : (decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State}
    (h : DR L L.k i σ s) : WP isa (sHat L A i) s (DR L L.k (i + 1) σ) := by
  have hc := W.s i hi
  simp only [sChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W.toDcWfB hp
  refine WP.mono (dec12At_okL hA L₀ rbx_na hc.1) fun s' ⟨hP, hq⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.dc, hk.r15, hk.u, fun k hk' => ?_⟩
  rcases (by omega_using [hk'] : k < i ∨ k = i) with hk' | rfl
  · exact hk.sh k hk'
  · rw [hP.pa rbx_cs]
    rw [slice_of h.dc.dk (show 384 * k + 384 ≤ L.dkLen by simp only [Kem.dkLen, Params.dkLen, Kem.k] at hi ⊢; omega_using [hi])]
      at hq
    rw [dcS, KPke.dkPke, slice_take _ (show 384 * k + 384 ≤ 384 * L.p.k by simp only [Kem.k] at hi; omega_using [hi])]
    exact hq

theorem s_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {i : Nat} (hi : i < L.k) :
    RelCT isa (R L (DR L L.k i)) (sHat L A i) fun _ _ => True := by
  have hc := W.s i hi
  simp only [sChk, Bool.and_eq_true] at hc
  exact rel2_of (dec12At_trL hA rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W.toDcWfB p₁ p₂ pub h₁.dc h₂.dc

/-! ## `m'` -/

/-- After K-PKE.Decrypt: `m'` at `M`. -/
structure DM (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = 1
  m : bytesAt s.mem (pa s (sc oM)) 32 = KPke.decM L.p (dcDk L σ) (dcC L σ)

/-- The rest of `decrypt`. -/
abbrev tail (L : Kem) (A : Arith) : Prog isa :=
  .seq (L.decMulAt A (pS 15) (pS L.k) (pS 0) (pS (2 * L.k)))
    (.seq (L.ddAt A.codecs (.r14, 32 * L.du * L.k) L.dv (pS 16)) (.seq (subAt A (pS 16) (pS 15)) (ceAt A.codecs (pS 16) 1 (sc oM))))

theorem tail_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    {σ : State} (hp : (decapsK L).pre σ) {s : State} (h : DR L L.k L.k σ s) : WP isa (tail L A) s (DM L σ) := by
  have hc := W.tail
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdm, hdd⟩, hk15⟩, hac⟩, htw⟩, hkc⟩, hk₁⟩ := hc
  have L₀ := h.dc.lay W.toDcWfB hp
  refine WP.seq (WP.mono (decMulAt_okL hA W.k34 L₀ rbx_na rbx_na rbx_na hdm
    (vecReduced_pS fun i hi => (h.sh i hi).1) (vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h.u i hi).1))
    fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e1 : vecAt s.mem (pa s (pS L.k)) L.k = (List.range L.k).map (dcS (KPke.dkPke L.p (dcDk L σ))) := by
    rw [vecAt_pS]; exact List.map_congr_left fun i hi => (h.sh i (List.mem_range.mp hi)).2
  have e2 : (vecAt s.mem (pa s (pS 0)) L.k).map ntt =
      (List.range L.k).map fun i => ntt (KPke.dcU L.p (dcC L σ) i) := by
    rw [vecAt_pS, List.map_map]
    exact List.map_congr_left fun i hi => by
      simp only [Function.comp, Nat.zero_add]; rw [(h.u i (List.mem_range.mp hi)).2]
  rw [e1, e2, KPke.dot_eq_dotK, ← hP₁.pa rbx_cs] at hp₁
  have L₁ := L₀.post hP₁.b (dcB_bases L)
  refine WP.seq (WP.mono (ddCall_okL (K.dd A.codecs) L₁ (d := L.dv) rbx_na hdd K.dv.2) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (dcB_bases L)
  have hc₂ : bytesAt s₁.mem (pa s₁ (.r14, 32 * L.du * L.k)) (32 * L.dv) =
      ((dcC L σ).drop (32 * L.du * L.k)).take (32 * L.dv) := by
    have k₁ := h.dc.step W.toDcWfB hp hP₁.b hk₁
    exact slice_of k₁.c (by simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc])
  rw [hc₂, ← hP₂.pa rbx_cs] at hp₂
  have hq₂ := L₁.keepPoly hP₂.b hk15 hp₁
  refine WP.seq (WP.mono (subAt_ok hA L₂ rbx_na hac hp₂.1 hq₂.1) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b (dcB_bases L)
  rw [hp₂.2, hq₂.2, ← hP₃.pa rbx_cs] at hp₃
  refine WP.mono (ceCall_okL (Codecs.ceI A.codecs) L₃ (d := 1) rbx_na htw (by decide) hp₃.1) fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)
  refine ⟨h.dc.step W.toDcWfB hp hP.b hkc, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [hP₄.pa rbx_cs, hb₄, hp₃.2, KPke.decM, KPke.kpkeDecrypt_eq]
    rfl

theorem tail_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (DR L L.k L.k)) (tail L A) fun _ _ => True := by
  have hc := W.tail
  simp only [tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdm, hdd⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩ := hc
  refine rel2_of (Q := fun x y => LRel (dcR L) (dcW L) x y ∧
      (VecReduced x.mem (pa x (pS L.k)) L.k ∧ VecReduced x.mem (pa x (pS 0)) L.k) ∧
      (VecReduced y.mem (pa y (pS L.k)) L.k ∧ VecReduced y.mem (pa y (pS 0)) L.k))
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (dcB_bases L)
    (RelCT.mono (decMulAt_trL hA W.k34 rbx_na rbx_na rbx_na hdm) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (decMulAt_okL hA W.k34 Lx rbx_na rbx_na rbx_na hdm hx.1 hx.2)
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16)) ∧ Reduced x.mem (pa x (pS 15))) (dcB_bases L)
      (RelCT.mono (ddCall_trL (K.dd A.codecs) (d := L.dv) rbx_na hdd K.dv.2) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL (K.dd A.codecs) Lx (d := L.dv) rbx_na hdd K.dv.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk15 hx⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16))) (dcB_bases L) (subAt_tr hA rbx_na hac)
      (fun x Lx hx => WP.mono (subAt_ok hA Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL (Codecs.ceI A.codecs) (d := 1) rbx_na htw (by decide)))))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨dc_lrel W.toDcWfB p₁ p₂ pub h₁.dc h₂.dc,
      ⟨vecReduced_pS fun i hi => (h₁.sh i hi).1, vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h₁.u i hi).1⟩,
      ⟨vecReduced_pS fun i hi => (h₂.sh i hi).1, vecReduced_pS fun i hi => by rw [Nat.zero_add]; exact (h₂.u i hi).1⟩⟩

end Decaps

end VG.Proof.MlKem.X86_64
