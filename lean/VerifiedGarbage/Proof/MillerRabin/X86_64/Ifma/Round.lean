module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Setup
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Window
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Lit

/-!
# The IFMA Miller–Rabin round: correctness

`ifma_ok`: the round of a layout, in its frame of the six callee-saved
registers: the setup (`setup_ok`), the vector code (`vec_ok`: `table_ok` and
`windows_ok` between Intel's MXCSR prologue and epilogue, which keep the
caller's MXCSR in `rbp`), and the flag and the registers back from the frame
(`finish_ok`); only the table arrays and the frame change. `code_correct`:
the dispatch on the candidate's size, `round mul` for the other sizes, with
MXCSR's control bits from `code_ctl`. `code_spSafe`, `code_depth` and
`code_ctl` are what `RoundImpl` needs besides.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52 at_)
open VG.Impl.Rsa.X86_64.PubIfma (arr pay1024 pay1536 pay2048 pay3072 pay4096)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.RsaKeyGen.X86_64.Candidate (aE aT0)
open VG.Proof.RsaKeyGen (mrA mrE wEnd)
open VG.Proof.MillerRabin.WindowK (kRun)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-! ## The MXCSR prologue and epilogue -/

/-- `withMx`'s shape, from the prologue's and the epilogue's blocks whole. -/
theorem wp_mx {S P L R V : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.block (S ++ P)) s fun s₁ => WP isa c s₁ fun s₂ => WP isa (.block (L ++ R ++ V)) s₂ Q) :
    WP isa (.seq (.seq (.block S) (.seq (.seq (.block P) (.seq c (.block L))) (.block R))) (.block V)) s Q := by
  refine WP.seq (WP.seq (WP.mono (WP.block_append_iff.mp h) fun s₁ h₁ => WP.seq (WP.seq (WP.mono h₁
    fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_)))))
  rw [List.append_assoc] at h₃
  exact WP.mono (WP.block_append_iff.mp h₃) fun s₄ h₄ => WP.block_append_iff.mp h₄

/-- The prologue: the caller's MXCSR, bits 31:16 cleared, in `rbp`, and
`MXCSR := 0x1FBF`. -/
theorem pro_ok {s : State} {B : Addr} {d Z : Nat} (hB : s.gpr .rbx = B) (hs : Scr s B Z) (hd : d + 8 ≤ Z) :
    WP isa (.block [.stmxcsr (at_ .rbx d), .mov32 .rbp (.mem (at_ .rbx d)), .alu32 .and .rbp (.imm 0xFFFF),
        .mov32 .rax (.imm 0x1FBF), .store32 (at_ .rbx (d + 4)) .rax, .ldmxcsr (at_ .rbx (d + 4)), .lfence]) s
      fun s' => s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
        s'.gpr .rbp = (s.mxcsr &&& 0xFFFF).setWidth 64 ∧ Keep [.rbp, .rax] s s' := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  have hst4 : InRegions s.wr (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld4 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (d + 4)) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d + 4) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rbp, .rax] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B d) s.mxcsr).writeW (off B (d + 4)) (0x1FBF : BitVec 32) ∧
      s'.gpr .rbp = (s.mxcsr &&& 0xFFFF).setWidth 64) (by
    xrun [ea_at'', hB, hst, hld, hst4, hld4, Mem.readW_writeW_self32]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩

/-- The epilogue: the saved MXCSR back from `rbp`. -/
theorem epi_ok {s : State} {B : Addr} {d Z : Nat} {v : BitVec 32} (hB : s.gpr .rbx = B) (hs : Scr s B Z)
    (hd : d + 8 ≤ Z) (hbp : s.gpr .rbp = (v &&& 0xFFFF).setWidth 64) :
    WP isa (.block (([.lfence] : List Instr) ++ ([.store32 (at_ .rbx d) .rbp, .ldmxcsr (at_ .rbx d)] : List Instr) ++
        ([.vop .vzeroupper] : List Instr))) s
      fun s' => s'.mem = s.mem.writeW (off B d) (v &&& 0xFFFF) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have hst : InRegions s.wr (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide); ⟨_, h, c⟩
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 4 :=
    let ⟨_, h, c⟩ := hs.region (d := d) (n := 4) (by omega_using [hd]) (by decide);
    ⟨_, List.mem_append_right _ h, c⟩
  simp only [List.cons_append, List.nil_append]
  xrun [ea_at'', hB, hst, hld, hbp, Mem.readW_writeW_self32, VG.Proof.Bignum.X86_64.AmmSym.and_ffff_hi]
  and_intros <;> rfl

/-! ## The flag and the callee-saved registers -/

theorem ea_rsp (t : State) (d : Int) : t.ea { base := .rsp, disp := d } = t.gpr .rsp + BitVec.ofInt 64 d :=
  rfl

theorem finish_ok {u : State} {B S : Addr} (hB : u.gpr .rbx = B) (hS : u.gpr .rsp = S)
    (hF : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (oF l)) 8)
    (h0 : InRegions (u.rd ++ u.wr) S 8) (h8 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 8) 8)
    (h16 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 16) 8)
    (h24 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 24) 8)
    (h32 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 32) 8)
    (h40 : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 40) 8) :
    WP isa (.block (finish l)) u fun t => t.gpr .rax = word u.mem B (oF l) &&& 1 ∧
      t.gpr .r15 = u.mem.readW S 64 ∧ t.gpr .r14 = u.mem.readW (S + 8#64) 64 ∧
      t.gpr .r13 = u.mem.readW (S + 16#64) 64 ∧ t.gpr .r12 = u.mem.readW (S + 24#64) 64 ∧
      t.gpr .rbp = u.mem.readW (S + 32#64) 64 ∧ t.gpr .rbx = u.mem.readW (S + 40#64) 64 ∧ t.mem = u.mem ∧
      Keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] u t := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun t =>
    t.gpr .rax = word u.mem B (oF l) &&& 1 ∧
      t.gpr .r15 = u.mem.readW S 64 ∧ t.gpr .r14 = u.mem.readW (S + 8#64) 64 ∧
      t.gpr .r13 = u.mem.readW (S + 16#64) 64 ∧ t.gpr .r12 = u.mem.readW (S + 24#64) 64 ∧
      t.gpr .rbp = u.mem.readW (S + 32#64) 64 ∧ t.gpr .rbx = u.mem.readW (S + 40#64) 64 ∧ t.mem = u.mem) (by
    unfold finish
    xrun [ea_at'', ea_rsp, BitVec.ofInt_ofNat, hB, hS, hF, h0, h8, h16, h24, h32, h40]) rfl)
    fun t ⟨⟨a, b, c, d, e, f, g, m⟩, k⟩ => ⟨a, b, c, d, e, f, g, m, k⟩

/-! ## The vector code -/

/-- A change within ranges of the area is within the area. -/
theorem area_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ size l) : Frm B [(0, size l)] m m' :=
  h.widen fun r hr' => ⟨_, List.mem_singleton_self _, Nat.zero_le _, by have := hr r hr'; omega_arith⟩

/-- A word of the workspace outside the area. -/
theorem hword_area {B H : Addr} {m m' : Mem} (f : Frm B [(0, size l)] m m') {d : Nat}
    (hd : ∀ x < 8, size l ≤ ofs B (off H d + BitVec.ofNat 64 x)) : word m' H d = word m H d :=
  Mem.readW_congr fun i hi => f _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := hd i (by omega_arith)
    exact .inr (by simp only [Nat.zero_add]; exact this)

/-- `Pre` through the MXCSR slots. -/
theorem pre_mx (hl : MrOk l) {B : Addr} {m m' : Mem} {c k bR : Nat} (hp : Pre l m B c k bR)
    (f : Frm B [(oMx l, 8)] m m') : Pre l m' B c k bR := by
  obtain ⟨-, hsz, h1, h2, h3, hTj, h4, h5, h6, h7, h8, -⟩ := MrOk.offs hl
  have e1 := hTj 1
  have e4 := hTj 4
  have hN : l.NB + 32 < 2 ^ 31 := by unfold size oF at hsz; omega_arith
  exact ⟨mod_frm hl hp.mod f (one_r (p := fun r => l.NB + 32 ≤ r.1) (by omega_arith)) hN,
    num_frm hl f hp.t0 (one_r (p := fun r => oT l 0 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oT l 0) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith),
    num_frm hl f hp.t1 (one_r (p := fun r => oT l 1 + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oT l 1) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith),
    num_frm hl f hp.kk (one_r (p := fun r => oS l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oS l) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith),
    num_frm hl f hp.m1 (one_r (p := fun r => oM1 l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oM1 l) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith),
    num_frm hl f hp.p1c (one_r (p := fun r => oP1c l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oP1c l) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith),
    num_frm hl f hp.m1c (one_r (p := fun r => oM1c l + l.NB ≤ r.1 ∨ r.1 + r.2 ≤ oM1c l) (.inl (by omega_arith)))
      (by unfold size oF at hsz; omega_arith)⟩

/-- The vector code: the table and the windows, under the MXCSR prologue and
epilogue; the flag at `oF`. -/
theorem vec_ok (hl : MrOk l) {s : State} {B H : Addr} {c k b : Nat}
    (hB : s.gpr .rbx = B) (hdi : s.gpr .rdi = H) (h12 : s.gpr .r12 = mask52) (hs : Scr s B (size l))
    (hodd : c % 2 = 1) (h3 : 3 ≤ c) (hc : c < 2 ^ (64 * l.W))
    (hp : Pre l s.mem B c k (b * 2 ^ (64 * l.W) % c))
    (erd : ∀ i < l.W + 1, InRegions (s.rd ++ s.wr) (off H (arr l aE + 8 * i)) 8)
    (ev : wv s.mem H (arr l aE) l.W = mrE c)
    (el : word s.mem H (arr l aE + 8 * l.W) = BitVec.twoPow 64 (mrA c % 64))
    (esep : ∀ i < l.W + 1, ∀ x < 8, size l ≤ ofs B (off H (arr l aE + 8 * i) + BitVec.ofNat 64 x)) :
    WP isa (vec l) s fun t =>
      word t.mem B (oF l) = mask (wEnd c (kRun 2 c b (mrE c) (32 * l.W) (32 * l.W))).2 ∧
      t.gpr .rbx = B ∧ t.gpr .rsp = s.gpr .rsp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frm B [(0, size l)] s.mem t.mem := by
  obtain ⟨-, hsz, h1, h2, h3', hTj, h4, h5, h6, h7, h8, -⟩ := MrOk.offs hl
  have e1 := hTj 1
  have e4 := hTj 4
  have hmx : oMx l + 8 ≤ size l := by unfold size oF; omega_arith
  have hF : oF l = oMx l + 8 := rfl
  have hz : size l = oF l + 8 := rfl
  have hn := hs.nowrap
  unfold vec withMx
  refine wp_mx (WP.mono (pro_ok (d := oMx l) hB hs hmx) fun s₁ ⟨m₁, bp₁, k₁⟩ => ?_)
  have O₁ : Outside B (oMx l) 8 s.mem s₁.mem := by
    rw [m₁]
    exact ((VG.Proof.Bignum.X86_64.AmmSym.writeW32_outside _ B _ (by omega_arith)).mono (by omega_arith)
      (by omega_arith)).trans ((VG.Proof.Bignum.X86_64.AmmSym.writeW32_outside _ B _ (by omega_arith)).mono
      (by omega_arith) (by omega_arith))
  have hB₁ : s₁.gpr .rbx = B := (k₁.gpr (by decide)).trans hB
  have h12₁ : s₁.gpr .r12 = mask52 := (k₁.gpr (by decide)).trans h12
  have hs₁ : Scr s₁ B (size l) := hs.congr k₁.2.2
  have F₁ : Frm B [(oMx l, 8)] s.mem s₁.mem := Frm.of_outside O₁ (List.mem_singleton_self _)
  rw [show VG.Impl.Bignum.X86_64.seqs (table l :: windows l) =
    .seq (table l) (VG.Impl.Bignum.X86_64.seqs (windows l)) from rfl]
  refine WP.seq (WP.mono (table_ok hl hB₁ h12₁ hs₁ hodd h3 hc (pre_mx hl hp F₁))
    fun t ⟨tb, F₂, g₂, r12₂, rd₂, wr₂, _⟩ => ?_)
  have g : ∀ r : Reg, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      r ≠ .r13 → t.gpr r = s₁.gpr r := g₂
  have FA : Frm B [(0, size l)] s.mem t.mem :=
    (area_frm F₁ (one_r (p := fun r => r.1 + r.2 ≤ size l) hmx)).trans
      (area_frm F₂ (one_r (p := fun r => r.1 + r.2 ≤ size l) (by have := (MrOk.ends hl).2.2; omega_arith)))
  have e₂ : WEnv l B H c k b t :=
    ⟨(g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans hB₁,
      (g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans ((k₁.gpr (by decide)).trans hdi), r12₂, hs₁.congr wr₂, tb, hodd, h3, hc,
      fun i hi => by rw [rd₂, wr₂, k₁.2.1, k₁.2.2]; exact erd i hi,
      by rw [← ev]; exact VG.Proof.Bignum.wv_congr fun i hi => hword_area FA (esep i (by omega_arith)),
      by rw [hword_area FA (esep l.W (by omega_arith))]; exact el, esep⟩
  refine WP.mono (windows_ok hl e₂) fun u ⟨fl, bp₃, bx₃, _, sp₃, _, rd₃, wr₃, _, F₃⟩ => ?_
  have bp : u.gpr .rbp = (s.mxcsr &&& 0xFFFF).setWidth 64 := by
    rw [bp₃, g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), bp₁]
  refine WP.mono (epi_ok (d := oMx l) bx₃ (hs.congr (by rw [wr₃, wr₂, k₁.2.2])) hmx bp)
    fun w ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  have O₄ : Outside B (oMx l) 4 u.mem w.mem := by
    rw [m₄]; exact VG.Proof.Bignum.X86_64.AmmSym.writeW32_outside _ B _ (by omega_arith)
  refine ⟨by rw [O₄.word (by omega_arith) (by omega_arith)]; exact fl, by rw [g₄]; exact bx₃, ?_,
    by rw [rd₄, rd₃, rd₂, k₁.2.1], by rw [wr₄, wr₃, wr₂, k₁.2.2], ?_⟩
  · rw [g₄, sp₃, g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), k₁.gpr (by decide)]
  · exact (FA.trans (area_frm F₃ (three_r (p := fun r => r.1 + r.2 ≤ size l) (by omega_arith) (by omega_arith)
      (by omega_arith)))).trans (area_frm (Frm.of_outside O₄ (List.mem_singleton_self _))
        (one_r (p := fun r => r.1 + r.2 ≤ size l) (by omega_arith)))

/-! ## The body of the frame -/

open VG.Impl.Bignum (sMinv)
open VG.Impl.Bignum.Public (aN aXm)
open VG.Impl.RsaKeyGen.X86_64.Candidate (aR1)

/-- The setup, the vector code and the flag, from the prepared workspace at
`H`: the passing flag in `rax`, the words at `rsp` in the callee-saved
registers; only the table arrays change. -/
theorem mid_ok (hl : MrOk l) {s : State} {H : Addr} {n c b : Nat}
    (hdi : s.gpr .rdi = H) (hwr : (⟨H, 8 * n⟩ : Region) ∈ s.wr) (hn : H.toNat + 8 * n ≤ 2 ^ 64)
    (hsz : arr l 27 ≤ 8 * n) (hc : wv s.mem H (arr l aN) l.W = c) (h3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hinv : ((word s.mem H (arr l aN)).toNat * (word s.mem H (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hr1 : wv s.mem H (arr l aR1) l.W = 2 ^ (64 * l.W) % c)
    (hx : wv s.mem H (arr l aXm) l.W = b * 2 ^ (64 * l.W) % c)
    (hE : VG.Proof.RsaKeyGen.X86_64.ECtx s.mem H l.W c)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsp) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 8#64) 8)
    (h16 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 16#64) 8)
    (h24 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 24#64) 8)
    (h32 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 32#64) 8)
    (h40 : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 40#64) 8) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (setup l ++ [vec l, .block (finish l)])) s fun t =>
      t.gpr .rax = mask (wEnd c (kRun 2 c b (mrE c) (32 * l.W) (32 * l.W))).2 &&& 1 ∧
      t.gpr .r15 = t.mem.readW (s.gpr .rsp) 64 ∧ t.gpr .r14 = t.mem.readW (s.gpr .rsp + 8#64) 64 ∧
      t.gpr .r13 = t.mem.readW (s.gpr .rsp + 16#64) 64 ∧ t.gpr .r12 = t.mem.readW (s.gpr .rsp + 24#64) 64 ∧
      t.gpr .rbp = t.mem.readW (s.gpr .rsp + 32#64) 64 ∧ t.gpr .rbx = t.mem.readW (s.gpr .rsp + 40#64) 64 ∧
      t.gpr .rsp = s.gpr .rsp ∧ t.wr = s.wr ∧
      Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem t.mem := by
  have hs : Scr s H (8 * n) := Scr.of_mem hwr hn
  have h27 : arr l (aT0 + 16) ≤ arr l 27 := by simp only [arr, aT0]; omega_arith
  have hn' : H.toNat + arr l (aT0 + 16) ≤ 2 ^ 64 := by omega_arith
  have hEa : arr l aE = arr l (aT0 + 16) := rfl
  have hE27 : arr l aE + 8 * (l.W + 1) ≤ arr l 27 := by simp only [arr, aE]; omega_arith
  obtain ⟨hd, hd', hBd⟩ := areaBase_ofs hl hn'
  have hsz' : size l < 2 ^ 31 := (MrOk.offs hl).2.1
  have hF8 : oF l + 8 ≤ size l := Nat.le_refl _
  refine VG.Proof.Bignum.X86_64.AmmSym.wp_seqs_app (by simp [setup]) (by simp) ?_
  refine WP.mono (setup_ok hl hdi hwr hn hsz hc h3 hinv hr1 hx)
    fun t₂ ⟨bx₂, r12₂, di₂, pre₂, F₂, g₂, rd₂, wr₂, _⟩ => ?_
  generalize ofs H (areaBase l H) = d at hd hd' hBd
  generalize hB : areaBase l H = B at bx₂ pre₂ hBd
  have hs₂ : Scr t₂ H (8 * n) := hs.congr wr₂
  have hsB : Scr t₂ B (size l) := by rw [hBd]; exact hs₂.sub (by omega_arith) (by unfold size; omega_arith)
  have hE₂ := hE.of_frm F₂ (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by
    simp only [VG.Proof.Bignum.slot, arr, aE, aT0] at *; omega_arith)) (by
      simp only [VG.Proof.Bignum.slot, arr, aE, aT0] at *; omega_arith)
  have esep : ∀ i < l.W + 1, ∀ x < 8, size l ≤ ofs B (off H (arr l aE + 8 * i) + BitVec.ofNat 64 x) :=
    fun i hi x hx => by
      rw [hBd, VG.Offset.add_add]
      simp only [ofs, off]
      rw [VG.Offset.sub_toNat H (by omega_arith) (by omega_arith)]
      omega_arith
  rw [show VG.Impl.Bignum.X86_64.seqs [vec l, .block (finish l)] = .seq (vec l) (.block (finish l)) from rfl]
  refine WP.seq (WP.mono (vec_ok hl bx₂ di₂ r12₂ hsB hodd h3 (by rw [← hc]; exact VG.Proof.Bignum.wv_lt _ _ _ _)
    pre₂ (fun i hi => hs₂.ld (by omega_arith)) hE₂.e hE₂.l esep)
    fun t₃ ⟨fl, bx₃, sp₃, rd₃, wr₃, F₃⟩ => ?_)
  have sp : t₃.gpr .rsp = s.gpr .rsp := by
    rw [sp₃, g₂ .rsp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have e : t₃.rd ++ t₃.wr = s.rd ++ s.wr := by rw [rd₃, wr₃, rd₂, wr₂]
  refine WP.mono (finish_ok (l := l) bx₃ sp ((hsB.congr wr₃).ld hF8) (by rw [e]; exact h0)
    (by rw [e]; exact h8) (by rw [e]; exact h16) (by rw [e]; exact h24) (by rw [e]; exact h32)
    (by rw [e]; exact h40)) fun t ⟨ax, r15, r14, r13, r12, bp, bx, mt, k⟩ => ?_
  rw [mt]
  refine ⟨by rw [ax, fl], r15, r14, r13, r12, bp, bx, (k.gpr (by decide)).trans sp, by rw [k.2.2, wr₃, wr₂], ?_⟩
  exact F₂.trans (frm_area F₃ hBd hd hd' hn' (one_r (p := fun r => r.1 + r.2 ≤ size l) (by omega_arith)))

/-! ## The frame -/

/-- A change of the table arrays is within the workspace. -/
theorem frm_ws {H : Addr} {N : Nat} {m m' : Mem} (h : Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] m m')
    (hN : arr l (aT0 + 16) ≤ N) : Frame [⟨H, N⟩] m m' := fun x hx => h x fun r hr => by
  rw [List.mem_singleton.mp hr]
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  have := arr_tab (l := l)
  exact .inr (by simp only [ofs]; omega_arith)

/-- A pushed word, through a change of the workspace. -/
theorem stack_word {m m' : Mem} {S H : Addr} {N : Nat} (f : Frame [⟨H, N⟩] m m')
    (hst : Region.Disjoint ⟨S - 120#64, 120⟩ ⟨H, N⟩) {j : Nat} (hj : j < 6) :
    m'.readW (S - BitVec.ofNat 64 (8 * (j + 1))) 64 = m.readW (S - BitVec.ofNat 64 (8 * (j + 1))) 64 :=
  f.readW (r := ⟨S - BitVec.ofNat 64 (8 * (j + 1)), 8⟩) (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hst.sub_left (VG.Offset.sub_below S (by omega_arith) (by omega_arith))) (by decide)

theorem sub48 (S : Addr) (j : Nat) (hj : j < 6) :
    S - 48#64 + BitVec.ofNat 64 (40 - 8 * j) = S - BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [VG.Offset.sub_ofNat_eq S (show 8 * (j + 1) ≤ 48 by omega_arith), show 48 - 8 * (j + 1) = 40 - 8 * j by
    omega_arith]

theorem res32 (p : Bool) : ((mask p &&& 1).setWidth 32).toNat = if p then 1 else 0 := by
  cases p <;> decide

theorem frame_head {S H : Addr} {N : Nat} :
    InRegions ([] ++ [(⟨S - 48#64, 48⟩ : Region), ⟨H, N⟩]) (S - 48#64) 8 :=
  ⟨_, List.mem_cons_self .., by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩

theorem frame_at {S : Addr} {H : Addr} {N : Nat} (d : Nat) (hd : d + 8 ≤ 48) :
    InRegions ([] ++ [(⟨S - 48#64, 48⟩ : Region), ⟨H, N⟩]) (S - 48#64 + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., VG.Offset.contains_base _ hd (by omega_arith)⟩

open VG.Proof.Bignum.X86_64.MontFn (numAt_eq)

/-- The round of a layout of the candidate's size. -/
theorem ifma_ok (hl : MrOk l) {s : State} (h : roundPre s)
    (hw : Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = l.W) :
    WP isa (ifma l) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ roundPost s t ∧
      Frame [⟨s.gpr .rsp - 48#64, 48⟩, ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩] s.mem t.mem := by
  obtain ⟨hdim, bm, hctx, hE, hodd, h3, hx⟩ := initial_ctx h
  obtain ⟨hrd, hwr, hn, hsp, hret, hstack, -, -⟩ := h
  rw [hw] at hdim hctx hE hodd h3 hx
  generalize hc : Proof.Rsa.Mont.numAt s.mem (s.gpr .rdi) l.W 0 = c at hctx hE hodd h3 hx
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * l.W)
  obtain ⟨b, hbc, hb⟩ := VG.Proof.MillerRabin.witness_exists hR hx
  have hsz : arr l 27 ≤ 8 * (s.gpr .rsi).toNat := by
    have := hdim.x
    simp only [arr, VG.Proof.Bignum.slot, VG.Impl.RsaKeyGen.X86_64.Candidate.aRm1] at this ⊢
    omega_arith
  have hz27 : arr l (aT0 + 16) ≤ (s.gpr .rsi).toNat * 8 := by simp only [arr, aT0] at hsz ⊢; omega_arith
  have hn8 : (s.gpr .rdi).toNat + 8 * (s.gpr .rsi).toNat ≤ 2 ^ 64 := by omega_arith
  have h48 : 8 * [Reg.rbx, .rbp, .r12, .r13, .r14, .r15].length ≤ (s.gpr .rsp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega_arith
  obtain ⟨hpf, hpv⟩ := pushRegs_mem s [.rbx, .rbp, .r12, .r13, .r14, .r15] (by decide) h48
  have mf : Frame [⟨s.gpr .rsp - 48#64, 48⟩] s.mem (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem := hpf
  have hst48 : Region.Disjoint ⟨s.gpr .rsp - 48#64, 48⟩ ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ :=
    hstack.sub_left (VG.Offset.sub_below _ (by decide) (by decide))
  have hws : ∀ x, (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region).Contains x 1 →
      (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem x = s.mem x := fun x hx' =>
    mf x fun r hr => by rw [List.mem_singleton.mp hr]; exact fun hc' => hst48 x hc' hx'
  have F0 : Frm (s.gpr .rdi) [(8 * (s.gpr .rsi).toNat, 2 ^ 64)] s.mem
      (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem := fun x hx' => hws x (by
    have h1 := hx' _ (List.mem_singleton_self _)
    have h2 := (x - s.gpr .rdi).isLt
    simp only [Region.Contains]; simp only [ofs] at h1; omega_arith)
  have F0s : ∀ r ∈ [(8 * (s.gpr .rsi).toNat, 2 ^ 64)], ∀ e, e ≤ 8 * (s.gpr .rsi).toNat → e ≤ r.1 := fun r hr e he => by
    rw [List.mem_singleton.mp hr]; exact he
  have sp₁ : (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).gpr .rsp = s.gpr .rsp - 48#64 := pushed_rsp _ _
  have rd₁ : (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).rd = [] := by rw [pushed_rd, hrd]
  have wr₁ : (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).wr =
      [⟨s.gpr .rsp - 48#64, 48⟩, ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩] := by rw [pushed_wr, hwr]; rfl
  have hc₁ : wv (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem (s.gpr .rdi) (arr l aN) l.W = c := by
    rw [F0.wv_eq (fun r hr => .inl (F0s r hr _ (by simp only [arr, aN] at hsz ⊢; omega_arith))) (by
      simp only [arr, aN] at hsz ⊢; omega_arith)]
    exact hctx.n
  have hinv₁ : ((word (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem (s.gpr .rdi) (arr l aN)).toNat *
      (word (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem (s.gpr .rdi) (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [F0.word_eq (fun r hr => .inl (F0s r hr _ (by simp only [arr, aN] at hsz ⊢; omega_arith))) (by
      simp only [arr, aN] at hsz ⊢; omega_arith),
      F0.word_eq (fun r hr => .inl (F0s r hr _ (by simp only [arr, sMinv] at hsz ⊢; omega_arith))) (by
      simp only [arr, sMinv] at hsz ⊢; omega_arith)]
    exact hctx.inv
  have hr1₁ : wv (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem (s.gpr .rdi) (arr l aR1) l.W =
      2 ^ (64 * l.W) % c := by
    rw [F0.wv_eq (fun r hr => .inl (F0s r hr _ (by simp only [arr, aR1] at hsz ⊢; omega_arith))) (by
      simp only [arr, aR1] at hsz ⊢; omega_arith)]
    exact hctx.r1
  have hx₁ : wv (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem (s.gpr .rdi) (arr l aXm) l.W =
      b * 2 ^ (64 * l.W) % c := by
    rw [F0.wv_eq (fun r hr => .inl (F0s r hr _ (by simp only [arr, aXm] at hsz ⊢; omega_arith))) (by
      simp only [arr, aXm] at hsz ⊢; omega_arith), ← Nat.mod_eq_of_lt hbc]
    exact hb
  have hE₁ := hE.of_frm F0 (fun r hr => .inl (F0s r hr _ (by
    simp only [arr, VG.Proof.Bignum.slot, aE] at hsz ⊢; omega_arith))) (by
    simp only [arr, VG.Proof.Bignum.slot, aE] at hsz ⊢; omega_arith)
  unfold ifma
  refine WP.frame (by decide) (by decide) (by decide) h48 ?_
  refine WP.mono (mid_ok hl (pushed_gpr _ _ (by decide)) (by rw [wr₁]; simp [Nat.mul_comm]) hn8 hsz hc₁ h3 hodd
    hinv₁ hr1₁ hx₁ hE₁ (by rw [sp₁, rd₁, wr₁]; exact frame_head) (by rw [sp₁, rd₁, wr₁]; exact frame_at 8 (by decide))
    (by rw [sp₁, rd₁, wr₁]; exact frame_at 16 (by decide)) (by rw [sp₁, rd₁, wr₁]; exact frame_at 24 (by decide))
    (by rw [sp₁, rd₁, wr₁]; exact frame_at 32 (by decide)) (by rw [sp₁, rd₁, wr₁]; exact frame_at 40 (by decide)))
    fun t ⟨ax, r15, r14, r13, r12, bp, bx, spt, wrt, Ft⟩ => ⟨spt, wrt, ?_⟩
  have F : Frame [⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩] (pushed [.rbx, .rbp, .r12, .r13, .r14, .r15] s).mem
      t.mem := frm_ws Ft hz27
  have sv : ∀ j (hj : j < 6), t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      s.gpr [Reg.rbx, .rbp, .r12, .r13, .r14, .r15][j] := fun j hj =>
    (stack_word F hstack hj).trans (hpv j (by simpa using hj))
  have st : ∀ j (hj : j < 6), t.mem.readW (s.gpr .rsp - 48#64 + BitVec.ofNat 64 (40 - 8 * j)) 64 =
      s.gpr [Reg.rbx, .rbp, .r12, .r13, .r14, .r15][j] := fun j hj => by rw [sub48 _ j hj]; exact sv j hj
  rw [sp₁] at r15 r14 r13 r12 bp bx
  have hEl : mrE c < (2 ^ 2) ^ (32 * l.W) := by
    rw [← hE.e, ← Nat.pow_mul, show 2 * (32 * l.W) = 64 * l.W by omega_arith]
    exact VG.Proof.Bignum.wv_lt _ _ _ _
  have hflag : (wEnd c (kRun 2 c b (mrE c) (32 * l.W) (32 * l.W))).2 = Proof.MillerRabin.Round.round c b :=
    VG.Proof.MillerRabin.WindowK.kEnd_eq b (by decide) (by decide) h3 hodd
      (VG.Proof.MillerRabin.Word32.mrA_le h3) hEl
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [popped_gpr _ _ _ (by decide) (by decide), bx]; exact st 0 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), bp]; exact st 1 (by decide)
    · rw [popped_rsp, spt, sp₁]; exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ (by decide) (by decide), r12]; exact st 2 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), r13]; exact st 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), r14]; exact st 4 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), r15]; exact sv 5 (by decide)
  · dsimp only [roundPost]
    rw [hw, hc]
    refine ⟨fun b' hb' => ?_, fun i hi _ _ ht => ?_⟩
    · have heq : Proof.MillerRabin.Round.round c b = Proof.MillerRabin.Round.round c b' := by
        apply VG.Proof.MillerRabin.round_eq_of_mont (by omega_arith) hR
        rw [← hb, ← hb']
        exact (numAt_eq s.mem _ l.W aXm).symm
      rw [popped_gpr _ _ _ (by decide) (by decide), ax, hflag, res32]
      exact congrArg (fun p : Bool => if p then 1 else 0) heq
    · have hi64 : i < 2 ^ 64 := by omega_arith
      have ho : (s.gpr .rdi + BitVec.ofNat 64 i - s.gpr .rdi).toNat = i := by
        rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
      rw [popped_mem]
      refine (Ft _ fun r hr => ?_).trans (hws _ ?_)
      · rw [List.mem_singleton.mp hr]
        simp only [ofs, ho]
        simp only [Proof.MillerRabin.Round.extended, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at ht
        simp only [arr, aT0, VG.Impl.Bignum.hdrBytes]
        omega_arith
      · simp only [Region.Contains, ho]; omega_arith
  · intro x hx
    rw [popped_mem]
    exact (F x fun r hr => by
        rw [List.mem_singleton.mp hr]; exact hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))).trans
      (mf x fun r hr => by rw [List.mem_singleton.mp hr]; exact hx _ (List.mem_cons_self ..))

/-! ## The dispatch -/

/-- `cmp w, n`, `w` from the header. -/
theorem isW_ok {t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (n : Nat)
    (hg : VG.Proof.Bignum.X86_64.Good t B Z w mi) (hZ : VG.Proof.Bignum.slot w 8 ≤ Z) (hn : n < 2 ^ 31)
    (hw : w < 2 ^ 31) :
    WP isa (.block (isW n)) t fun u => u.zf = some (decide (w = n)) ∧ u.mem = t.mem ∧ Keep [.rax] t u := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := VG.Proof.Bignum.hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun u => u.zf = some (decide (w = n)) ∧
    u.mem = t.mem) (by
    unfold isW
    xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hg.rdi, VG.Proof.Bignum.X86_64.hdrOff,
      hl VG.Impl.Bignum.sW (by decide), hg.hdr.hw, VG.Proof.Bignum.X86_64.AmmSym.se_ofNat hn]
    and_intros
    rw [VG.Proof.Bignum.X86_64.ofNat_sub_beq (by omega_arith) (by omega_arith)]) rfl)
    fun u ⟨⟨z, m⟩, k⟩ => ⟨z, m, k⟩

theorem pre_congr {s u : State} (hm : u.mem = s.mem) (k : Keep [.rax] s u) (h : roundPre s) : roundPre u := by
  have hdi : u.gpr .rdi = s.gpr .rdi := k.gpr (by decide)
  have hsi : u.gpr .rsi = s.gpr .rsi := k.gpr (by decide)
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  unfold roundPre at h ⊢
  rw [hm, hdi, hsi, hsp, k.2.1, k.2.2]
  exact h

theorem post_congr {s u t : State} (hm : u.mem = s.mem) (k : Keep [.rax] s u) (h : roundPost u t) :
    roundPost s t := by
  have hdi : u.gpr .rdi = s.gpr .rdi := k.gpr (by decide)
  have hsi : u.gpr .rsi = s.gpr .rsi := k.gpr (by decide)
  unfold roundPost at h ⊢
  rw [hm, hdi, hsi] at h
  exact h

/-- What the round's callers need of a run: the callee-saved registers, the
return address and `roundPost`. -/
def Out (s t : State) : Prop :=
  (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 ∧
    roundPost s t

/-- A layout's round, from a state of the dispatch. -/
theorem ifma_out (hl : MrOk l) {s u : State} (h : roundPre s) (hm : u.mem = s.mem) (k : Keep [.rax] s u)
    (hw : Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = l.W) : WP isa (ifma l) u (Out s) := by
  have hu := pre_congr hm k h
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.mono (ifma_ok hl hu (by rw [hm, k.gpr (by decide)]; exact hw)) fun t ⟨hr, hp, hf⟩ => ?_
  refine ⟨fun r hr' => (hr r hr').trans (k.gpr fun h' => by
    simp only [List.mem_singleton] at h'; subst h'; revert hr'; decide), ?_, post_congr hm k hp⟩
  rw [← hm, ← hsp]
  refine hf.readW (r := ⟨u.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr' => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · have ha : (⟨u.gpr .rsp, 8⟩ : Region) = ⟨(u.gpr .rsp - 48#64) + BitVec.ofNat 64 48, 8⟩ := by
      rw [show BitVec.ofNat 64 48 = 48#64 from rfl, BitVec.sub_add_cancel]
    rw [ha]
    exact VG.Offset.disjoint_base (u.gpr .rsp - 48#64) (by decide : 48 ≤ 48) (by decide : 48 + 8 ≤ 2 ^ 64)
  · exact hu.2.2.2.2.1

/-- The fallback, from a state of the dispatch. -/
theorem round_out (v : RoundArith) {s u : State} (h : roundPre s) (hm : u.mem = s.mem) (k : Keep [.rax] s u) :
    WP isa (VG.Impl.MillerRabin.X86_64.round v.mm) u (Out s) := by
  obtain ⟨tr, t, he, ⟨hr, hra, -⟩, hp⟩ := v.round_correct u (pre_congr hm k h)
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine ⟨tr, t, he, fun r hr' => (hr r hr').trans (k.gpr fun h' => by
    simp only [List.mem_singleton] at h'; subst h'; revert hr'; decide), ?_, post_congr hm k hp⟩
  rw [← hm, ← hsp]; exact hra

/-- The round with the IFMA layouts, `round mul` otherwise. -/
theorem code_wp (v : RoundArith) (s : State) (h : roundPre s) : WP isa (code v.mm) s (Out s) := by
  obtain ⟨hdim, bm, hctx, -⟩ := initial_ctx h
  have hg := hctx.good
  have hw31 : Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) < 2 ^ 31 := by have := hdim.w128; omega_arith
  unfold code
  have m₀ : s.mem = s.mem := rfl
  have k₀ : Keep [.rax] s s := Keep.refl _ _
  refine WP.seq (WP.mono (isW_ok 16 hg hdim.z (by decide) hw31) fun u1 ⟨z1, m1, k1⟩ => ?_)
  have m1' : u1.mem = s.mem := m1.trans m₀
  have k1' : Keep [.rax] s u1 := (k₀.trans k1).mono (by decide)
  refine WP.ite (decide (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = 16)) (by simp only [eval, z1])
    (fun hb => ifma_out (.inl rfl) h m1' k1' (of_decide_eq_true hb)) (fun _ => ?_)
  have g1 : VG.Proof.Bignum.X86_64.Good u1 (s.gpr .rdi) ((s.gpr .rsi).toNat * 8)
      (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi)) (word s.mem (s.gpr .rdi) (8 * sMinv)) :=
    ⟨hg.scr.congr k1'.2.2, (k1'.gpr (by decide)).trans hg.rdi, by rw [m1']; exact hg.hdr⟩
  refine WP.seq (WP.mono (isW_ok 24 g1 hdim.z (by decide) hw31) fun u2 ⟨z2, m2, k2⟩ => ?_)
  have m2' : u2.mem = s.mem := m2.trans m1'
  have k2' : Keep [.rax] s u2 := (k1'.trans k2).mono (by decide)
  refine WP.ite (decide (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = 24)) (by simp only [eval, z2])
    (fun hb => ifma_out (.inr (.inl rfl)) h m2' k2' (of_decide_eq_true hb)) (fun _ => ?_)
  have g2 : VG.Proof.Bignum.X86_64.Good u2 (s.gpr .rdi) ((s.gpr .rsi).toNat * 8)
      (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi)) (word s.mem (s.gpr .rdi) (8 * sMinv)) :=
    ⟨hg.scr.congr k2'.2.2, (k2'.gpr (by decide)).trans hg.rdi, by rw [m2']; exact hg.hdr⟩
  refine WP.seq (WP.mono (isW_ok 32 g2 hdim.z (by decide) hw31) fun u3 ⟨z3, m3, k3⟩ => ?_)
  have m3' : u3.mem = s.mem := m3.trans m2'
  have k3' : Keep [.rax] s u3 := (k2'.trans k3).mono (by decide)
  refine WP.ite (decide (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = 32)) (by simp only [eval, z3])
    (fun hb => ifma_out (.inr (.inr (.inl rfl))) h m3' k3' (of_decide_eq_true hb)) (fun _ => ?_)
  have g3 : VG.Proof.Bignum.X86_64.Good u3 (s.gpr .rdi) ((s.gpr .rsi).toNat * 8)
      (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi)) (word s.mem (s.gpr .rdi) (8 * sMinv)) :=
    ⟨hg.scr.congr k3'.2.2, (k3'.gpr (by decide)).trans hg.rdi, by rw [m3']; exact hg.hdr⟩
  refine WP.seq (WP.mono (isW_ok 48 g3 hdim.z (by decide) hw31) fun u4 ⟨z4, m4, k4⟩ => ?_)
  have m4' : u4.mem = s.mem := m4.trans m3'
  have k4' : Keep [.rax] s u4 := (k3'.trans k4).mono (by decide)
  refine WP.ite (decide (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = 48)) (by simp only [eval, z4])
    (fun hb => ifma_out (.inr (.inr (.inr (.inl rfl)))) h m4' k4' (of_decide_eq_true hb)) (fun _ => ?_)
  have g4 : VG.Proof.Bignum.X86_64.Good u4 (s.gpr .rdi) ((s.gpr .rsi).toNat * 8)
      (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi)) (word s.mem (s.gpr .rdi) (8 * sMinv)) :=
    ⟨hg.scr.congr k4'.2.2, (k4'.gpr (by decide)).trans hg.rdi, by rw [m4']; exact hg.hdr⟩
  refine WP.seq (WP.mono (isW_ok 64 g4 hdim.z (by decide) hw31) fun u5 ⟨z5, m5, k5⟩ => ?_)
  have m5' : u5.mem = s.mem := m5.trans m4'
  have k5' : Keep [.rax] s u5 := (k4'.trans k5).mono (by decide)
  exact WP.ite (decide (Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = 64)) (by simp only [eval, z5])
    (fun hb => ifma_out (.inr (.inr (.inr (.inr rfl)))) h m5' k5' (of_decide_eq_true hb)) (fun _ => round_out v h m5' k5')

/-! ## The round's properties as a backend's -/

/-- What the backend needs of a layout's code, checked together (the kernel
builds the code once for both). -/
theorem ifma_checks (hl : MrOk l) :
    ctlOk (ifma l) = true ∧ (ifma l).all (fun i => !isa.writesSp i) = true := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> lit_decide

theorem ifma_ctl (hl : MrOk l) : ctlOk (ifma l) = true := (ifma_checks hl).1

theorem code_ctl (v : RoundArith) : ctlOk (code v.mm) = true :=
  ctlOk_seq_of (by decide) (ctlOk_ite_of (ifma_ctl (.inl rfl)) (ctlOk_seq_of (by decide)
    (ctlOk_ite_of (ifma_ctl (.inr (.inl rfl))) (ctlOk_seq_of (by decide)
      (ctlOk_ite_of (ifma_ctl (.inr (.inr (.inl rfl)))) (ctlOk_seq_of (by decide)
        (ctlOk_ite_of (ifma_ctl (.inr (.inr (.inr (.inl rfl))))) (ctlOk_seq_of (by decide)
          (ctlOk_ite_of (ifma_ctl (.inr (.inr (.inr (.inr rfl))))) (ctlOk_of_noLoad v.mxSafe))))))))))

/-- The round with the IFMA layouts, `round mul` otherwise. -/
theorem code_correct (v : RoundArith) (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa (code v.mm) s tr t ∧ abiPreserved s t ∧ roundPost s t := by
  obtain ⟨tr, t, he, hr, hra, hp⟩ := code_wp v s h
  exact ⟨tr, t, he, ⟨hr, hra, Exec.ctl (code_ctl v) he⟩, hp⟩

theorem ifma_sp (hl : MrOk l) : (ifma l).all (fun i => !isa.writesSp i) = true := (ifma_checks hl).2

theorem all_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.seq a b).all p = true := by
  show (a.all p && b.all p) = true; rw [ha, hb]; rfl

theorem all_ite {p : Instr → Bool} {c : Cond} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.ite c a b).all p = true := by
  show (a.all p && b.all p) = true; rw [ha, hb]; rfl

theorem code_spSafe (v : RoundArith)
    (hr : (VG.Impl.MillerRabin.X86_64.round v.mm).all (fun i => !isa.writesSp i) = true) :
    (code v.mm).all (fun i => !isa.writesSp i) = true :=
  all_seq (by decide) (all_ite (ifma_sp (.inl rfl)) (all_seq (by decide) (all_ite (ifma_sp (.inr (.inl rfl)))
    (all_seq (by decide) (all_ite (ifma_sp (.inr (.inr (.inl rfl))))
      (all_seq (by decide) (all_ite (ifma_sp (.inr (.inr (.inr (.inl rfl)))))
        (all_seq (by decide) (all_ite (ifma_sp (.inr (.inr (.inr (.inr rfl))))) hr)))))))))

theorem ifma_depth (hl : MrOk l) : (ifma l).x86_64Depth = 48 := by
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> lit_decide

theorem code_depth (v : RoundArith) (hd : (VG.Impl.MillerRabin.X86_64.round v.mm).x86_64Depth ≤ 120) :
    (code v.mm).x86_64Depth ≤ 120 := by
  show max 0 (max (ifma pay1024).x86_64Depth (max 0 (max (ifma pay1536).x86_64Depth
    (max 0 (max (ifma pay2048).x86_64Depth (max 0 (max (ifma pay3072).x86_64Depth
      (max 0 (max (ifma pay4096).x86_64Depth (VG.Impl.MillerRabin.X86_64.round v.mm).x86_64Depth))))))))) ≤ 120
  rw [ifma_depth (.inl rfl), ifma_depth (.inr (.inl rfl)), ifma_depth (.inr (.inr (.inl rfl))),
    ifma_depth (.inr (.inr (.inr (.inl rfl)))), ifma_depth (.inr (.inr (.inr (.inr rfl))))]
  omega_arith

end VG.Proof.MillerRabin.X86_64.Ifma
