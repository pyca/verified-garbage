module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
public import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgfLoop
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.Mgf1.Bytes
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.RsaPss.Arm.CtXor

/-!
# RSAES-OAEP on ARMv7: the indirect calls of a table's functions

`tcall_vp`, `tcallF_vp`: the call of a table's function `j`
(`Impl.RsaOaep.Arm.tcall`, `tcallF`: its address into `r4`, then `blx r4`,
alone or in the frame of its stack arguments) is a piece (`VP`) as the call
of the function it reaches is, when both runs reach it at the same address,
with the same `sp`. `VP.syms`: a piece keeps the addresses of the statics,
which the calls need to know which function the table's address names.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm
open VG.Proof.Rsa.Arm.Recover (VP Two)
open VG.Impl.RsaOaep.Arm (tcall tcallF tload)

/-- A piece keeps the addresses of the statics. -/
theorem VP.syms {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) :
    VP (fun σ s => F σ s ∧ s.syms = σ.syms) c (fun σ s => G σ s ∧ s.syms = σ.syms) := by
  refine ⟨fun σ s hs => WP.mono_syms (h.wp σ s hs.1) fun _ hq sy => ⟨hq, sy.trans hs.2⟩, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨h₁, y₁⟩, ⟨h₂, y₂⟩⟩ e₁ e₂
  have r := ((h.ct.mono (P' := fun a b => F σ₁ a ∧ F σ₂ b) (fun a b hab => ⟨σ₁, σ₂, hab⟩) fun _ _ q => q).wp
    (F₁ := G σ₁) (F₂ := G σ₂) fun _ _ hh => ⟨h.wp _ _ hh.1, h.wp _ _ hh.2⟩) _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, ⟨r.2.2.1, (Exec.syms e₁).trans y₁⟩, ⟨r.2.2.2, (Exec.syms e₂).trans y₂⟩⟩

theorem push_some_gpr {rs : List Reg} {s u : State} (h : isa.push (.push rs) s = some u) :
    u.gpr = s.gpr ∧ u.syms = s.syms := by
  simp only [isa, push] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- The call of the table's function `j`, among `ts`: after the load of its
address into `r4` (`hl`), it reaches `(n, c)` (`ht`), at the same address in
both runs (`hpub`). -/
theorem tcall_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)}
    {n : String} {c : Prog isa} (hne : ts ≠ []) (hl : VP F (.block (tload j)) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .r4).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .r4 = s₂.gpr .r4)
    (h : VP F₁ (.call n c) G) : VP F (tcall j ts) G := by
  refine VP.seq hl ⟨fun σ s hs => WP.icalls_of_call rfl (ht σ s hs) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨_, rfl, ?_, ht σ₁ s₁ h₁, ?_, rfl⟩
  · show some ((s₂.gpr .r4).setWidth 64) = some ((s₁.gpr .r4).setWidth 64)
    rw [hpub _ _ _ _ h₁ h₂]
  · rw [hpub _ _ _ _ h₁ h₂]; exact ht σ₂ s₂ h₂

/-- The same, in a frame pushing `rs`, with the same `sp` in both runs. -/
theorem tcallF_vp {F F₁ G : State → State → Prop} {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg}
    {k : Nat} {n : String} {c : Prog isa} (hne : ts ≠ []) (hl : VP F (.block (tload j)) F₁)
    (ht : ∀ σ s, F₁ σ s → icallTarget isa s ((s.gpr .r4).setWidth 64) ts = some (n, c))
    (hpub : ∀ σ₁ σ₂ s₁ s₂, F₁ σ₁ s₁ → F₁ σ₂ s₂ → s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp)
    (h : VP F₁ (.frame (.push rs) (.call n c) (.pop .r1 k)) G) : VP F (tcallF j ts rs k) G := by
  have tgt : ∀ σ s u, F₁ σ s → isa.push (.push rs) s = some u →
      icallTarget isa u ((u.gpr .r4).setWidth 64) ts = some (n, c) := fun σ s u hs hp => by
    obtain ⟨g, y⟩ := push_some_gpr hp
    rw [g, icallTarget_congr (s₂ := s) fun q _ => by
      show (u.syms q.1).setWidth 64 = (s.syms q.1).setWidth 64
      rw [y]]
    exact ht σ s hs
  refine VP.seq hl ⟨fun σ s hs => WP.frame_icalls_of_call (fun u hp => ⟨_, rfl, tgt σ s u hs hp⟩) (h.wp σ s hs), ?_⟩
  obtain ⟨p, ts', rfl⟩ : ∃ p ts', ts = p :: ts' := by
    cases ts with
    | nil => exact absurd rfl hne
    | cons p ts' => exact ⟨p, ts', rfl⟩
  refine RelCT.frame_icalls_of_call h.ct fun s₁ s₂ ⟨σ₁, σ₂, h₁, h₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
  · show addrs (.push rs) s₁ = addrs (.push rs) s₂
    simp only [addrs, (hpub _ _ _ _ h₁ h₂).2]
  · have e₁ := tgt σ₁ s₁ _ h₁ hp₁
    have e₂ := tgt σ₂ s₂ _ h₂ hp₂
    have g : u₂.gpr .r4 = u₁.gpr .r4 := by
      rw [(push_some_gpr hp₁).1, (push_some_gpr hp₂).1, (hpub _ _ _ _ h₁ h₂).1]
    rw [g] at e₂
    exact ⟨_, rfl, congrArg (fun v => some (BitVec.setWidth 64 v)) g, e₁, e₂, rfl⟩

end VG.Proof.RsaOaep.Arm

/-!
# RSAES-OAEP on ARMv7: `dst ⊕= MGF1(src, dstLen)`, with MGF1's table

`OHash`: a hash function as RSAES-OAEP on ARMv7 uses it, its streaming
functions verified (`Pbkdf2.Stream.Arm.HashOK`) and the hash function as
RSA's padding takes it, with a digest length the functions taking a table
branch on (`lens`); from the RSASSA-PSS one (`OHash.ofPss`).

`mgf_vp`: with `src` (`sl` bytes at `so`) and `dst` (`dl` bytes at `dOff`)
in `EM`'s place in our part of `scratch`, their addresses and lengths in
their slots, `mgfXor f j` XORs MGF1's mask of `src` into `dst`, one digest
of `src ‖ C` (by the streaming `init`, two `update`s and `finalize`) at a
time, with the hash function `g` of the table that is our argument `j` (at
`p`, `L.argv`'s word `j`): in every run, the table holds `g`'s functions'
addresses (`ai`, `au`, `af`, the same in both runs) and its digest length
(`TabFacts`), and an indirect call of `f`'s functions to their address
reaches them (`TabOK`), so each call through the table (`tcall_vp`,
`tcallF_vp`) runs as `g`'s (`tcallI_vp`, `tcallK_vp`). The table's address
and digest length are in their slots (`sTab`, `sHl`) during the rounds, and
every stage keeps the addresses of the statics (`VP.syms`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa countLoop sCtr sDone ctrPut xorBody mgfInit)
open VG.Impl.Pbkdf2.Stream.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-- A hash function, as RSAES-OAEP on ARMv7 uses it. -/
structure OHash where
  H : Hash
  ok : HashOK H
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  glen : G.len = H.D
  valid : Proof.Mgf1.Valid G
  /-- Its digest length is one the functions taking a table branch on. -/
  lens : H.D ∈ Impl.RsaOaep.Arm.lens

/-- The RSASSA-PSS hash function's streaming functions. -/
def OHash.ofPss (h : PssHash) (hD : h.H.md.st.D ∈ Impl.RsaOaep.Arm.lens := by decide) : OHash :=
  ⟨h.H.md.st, h.ok.stream, h.G, h.hash, h.glen, h.valid, hD⟩

namespace OHash

variable (g : OHash)

theorem D_pos : 0 < g.H.D := g.ok.hD0
theorem D_le : g.H.D ≤ 64 := by have := g.ok.hDF; have := g.ok.hF; omega_arith
theorem DF : g.H.D ≤ g.H.F := g.ok.hDF
theorem F_le : g.H.F ≤ 64 := g.ok.hF
theorem S_le : g.H.S ≤ 256 := g.ok.hSB
theorem Wb_le : g.ok.Wb ≤ 512 := by have := g.ok.hWb; have := g.ok.hW; omega_arith

/-- A byte of the mask, in the digest of `src ‖ C` for the counter `c`. -/
theorem mask_byte {seed : List Byte} {dl c i : Nat} (hi : i < dl) (h₁ : c * g.H.D ≤ i) (h₂ : i < c * g.H.D + g.H.D) :
    (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 = (g.ok.SH.H.hash (seed ++ Spec.Rsa.i2osp c 4)).getD (i - c * g.H.D) 0 := by
  have hD0 := g.D_pos
  rw [Proof.Mgf1.mgf1_getD g.valid _ hi, g.glen, ← g.hash]
  have e1 : i / g.H.D = c := Nat.div_eq_of_lt_le h₁ (by rw [Nat.succ_mul]; omega_arith)
  have e2 : i % g.H.D = i - c * g.H.D := by
    have := Nat.mod_add_div i g.H.D
    rw [e1, Nat.mul_comm] at this
    omega_arith
  rw [e1, e2]

end OHash

/-! ## The table -/

/-- The table's word at `p + o`. -/
abbrev tA (p : BitVec 32) (o : Nat) : Addr := State.addr (p + BitVec.ofNat 32 o)

/-- At `p` in `m`, the addresses `sy` gives `G`'s `init`, `update` and
`finalize`. -/
def TabMem (G : Hash) (sy : String → BitVec 32) (p : BitVec 32) (m : Mem) : Prop :=
  m.readW (tA p 0) 32 = sy G.initN ∧ m.readW (tA p 4) 32 = sy G.updN ∧ m.readW (tA p 8) 32 = sy G.finN

/-- An indirect call of `f`'s functions, at the addresses `sy` gives, to the
address of one of `G`'s functions reaches it. -/
structure TabOK (G : Hash) (f : Fns) (sy : String → BitVec 32) : Prop where
  i : f.init.find? (fun q => (sy q.1).setWidth 64 == (sy G.initN).setWidth 64) = some (G.initN, G.initC)
  u : f.upd.find? (fun q => (sy q.1).setWidth 64 == (sy G.updN).setWidth 64) = some (G.updN, G.updC)
  f : f.fin.find? (fun q => (sy q.1).setWidth 64 == (sy G.finN).setWidth 64) = some (G.finN, G.finC)

/-- What MGF1 needs of its table at `p`, in the run from `σ`: an indirect
call reaches `G`'s functions, at `ai`, `au` and `af`, whose addresses the
table holds, then its digest length. -/
structure TabFacts (G : Hash) (f : Fns) (p ai au af : BitVec 32) (σ : State) : Prop where
  ok : TabOK G f σ.syms
  mem : TabMem G σ.syms p σ.mem
  d : σ.mem.readW (tA p 16) 32 = BitVec.ofNat 32 G.D
  ai : σ.syms G.initN = ai
  au : σ.syms G.updN = au
  af : σ.syms G.finN = af

/-- A word of a buffer only read, as on entry. -/
theorem St_roW {L : Lay} {σ s : State} (h : L.St σ s) {R : Region} (hR : R ∈ L.ro) {a : Addr}
    (hc : R.Contains a 4) : s.mem.readW a 32 = σ.mem.readW a 32 := by
  refine h.frame.readW hc (fun r hr => ?_) (by decide)
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr | rfl
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (h.ok.wro r hr R (List.mem_append_left _ hR)).symm
  · exact ((h.ok.stk R (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- A word of a buffer only read may be read. -/
theorem St_roR {L : Lay} {σ s : State} (h : L.St σ s) {R : Region} (hR : R ∈ L.ro) {a : Addr}
    (hc : R.Contains a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  ⟨R, by rw [h.rd, h.ok.rd]; exact List.mem_append_left _ (List.mem_append_left _ hR), hc⟩

variable {L : Lay} {scr : BitVec 32} (g : OHash) {f : Fns} {j : Nat} {ai au af : BitVec 32}

/-- The bytes at `scr + o` as a list. -/
theorem bytesAt_scr (hg : Geo L scr) {m : Mem} {o n : Nat} (h : o + n ≤ oRsa) {xs : List Byte} (hl : xs.length = n)
    (hx : ∀ i < n, m (sa scr (o + i)) = xs.getD i 0) :
    Spec.Sha256.bytesAt m (State.addr (scr + BitVec.ofNat 32 o)) n = xs := by
  apply List.ext_getElem (by simp [Spec.Sha256.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Sha256.bytesAt, List.getElem_map, List.getElem_range]
  have e := hx i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at e
  rw [← e]
  by_cases hn : n = 0
  · omega_arith
  rw [hg.addr (by omega_arith), sa, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-! ## The parameters -/

/-- What `mgfXor` writes. -/
abbrev mgfW (L : Lay) (scr : BitVec 32) (dOff dl : Nat) : List Region :=
  [sR scr oSt g.H.S, sR scr oCtr 4, sR scr oDig g.H.F, sR scr oW g.ok.Wb, L.LOW, sR scr dOff dl, slotR L sCtr,
    slotR L sDone, slotR L sTab, slotR L sHl]

/-- The parameters of `mgfXor f j`: `src` (`sl` bytes at `so`) and `dst`
(`dl` bytes at `dOff`), apart, in `EM`'s place; their slots, what the caller
keeps (`Inv`), and the table that is our argument `j`: in a buffer only
read (`tbl`), with what MGF1 needs of it in every run (`tab`). -/
structure MP (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (seed : State → List Byte)
    (Inv : State → Mem → Prop) (f : Fns) (j : Nat) (ai au af : BitVec 32) : Prop where
  hg : Geo L scr
  sl0 : 0 < sl
  dl0 : 0 < dl
  fs : so + sl ≤ oBuf
  fd : dOff + dl ≤ oBuf
  sep : so + sl ≤ dOff ∨ dOff + dl ≤ so
  sd : ∀ σ, (seed σ).length = sl
  I : ∀ σ m m', Inv σ m → Frame (mgfW g L scr dOff dl) m m' → Inv σ m'
  src : ∀ σ m, Inv σ m → m.readW (L.fr sSrc) 32 = scr + BitVec.ofNat 32 so
  srcL : ∀ σ m, Inv σ m → m.readW (L.fr sSrcLen) 32 = BitVec.ofNat 32 sl
  dst : ∀ σ m, Inv σ m → m.readW (L.fr sDst) 32 = scr + BitVec.ofNat 32 dOff
  dstL : ∀ σ m, Inv σ m → m.readW (L.fr sDstLen) 32 = BitVec.ofNat 32 dl
  hj : j < L.argv.length
  tbl : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 20 → R.Contains (tA (L.argv.getD j 0) o) 4
  tab : ∀ σ m, Inv σ m → TabFacts g.H f (L.argv.getD j 0) ai au af σ
  fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []

/-- The memory before iteration `c`: the table's address and digest length,
the counter, the bytes masked, `dst` masked up to `c hLen` bytes, and
`src`. -/
structure MB (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  tabS : m.readW (L.fr sTab) 32 = L.argv.getD j 0
  hlS : m.readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

variable {so sl dOff dl : Nat} {seed : State → List Byte} {Inv : State → Mem → Prop} {dstv : State → Nat → Byte}

/-- What the caller keeps, and the memory before iteration `c`. -/
abbrev MI (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : State → Nat → Byte)
    (seed : State → List Byte) (Inv : State → Mem → Prop) (σ : State) (m : Mem) : Prop :=
  Inv σ m ∧ MB g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) m

/-- What misses the slots of the counter and of the bytes masked, `dst`, `src`
and the table's slots. -/
abbrev Away (L : Lay) (scr : BitVec 32) (so sl dOff dl : Nat) (r : Region) : Prop :=
  (slotR L sCtr).Disjoint r ∧ (slotR L sDone).Disjoint r ∧ (sR scr dOff dl).Disjoint r ∧ (sR scr so sl).Disjoint r ∧
    (slotR L sTab).Disjoint r ∧ (slotR L sHl).Disjoint r

namespace MP

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af)
include P

theorem keepB {c : Nat} {dv : Nat → Byte} {sd : List Byte} {m m' : Mem} {rs : List Region}
    (hm : MB g (j := j) L scr so sl dOff dl c dv sd m) (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) : MB g (j := j) L scr so sl dOff dl c dv sd m' := by
  have := P.fs; have := P.fd
  exact ⟨slot_keep hf (fun r hr => (hs r hr).2.2.2.2.1) hm.tabS, slot_keep hf (fun r hr => (hs r hr).2.2.2.2.2) hm.hlS,
    slot_keep hf (fun r hr => (hs r hr).1) hm.ctr, slot_keep hf (fun r hr => (hs r hr).2.1) hm.done,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.1) (by oomega) hm.dx,
    sbytes_keep hf (fun r hr => (hs r hr).2.2.2.1) (by oomega) hm.sd⟩

theorem keep {c : Nat} {σ : State} {m m' : Mem} {rs : List Region}
    (hm : MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m) (hf : Frame rs m m')
    (hsub : ∀ r ∈ rs, r ∈ mgfW g L scr dOff dl) (hs : ∀ r ∈ rs, Away L scr so sl dOff dl r) :
    MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m' :=
  ⟨P.I σ m m' hm.1 (hf.mono hsub), P.keepB hm.2 hf hs⟩

/-- A range of our part of `scratch` from `oSt` on misses them. -/
theorem away_hi {o n : Nat} (ho : oSt ≤ o) (hn : o + n ≤ oRsa) : Away L scr so sl dOff dl (sR scr o n) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨P.hg.slot ok hn (by rw [P.hg.F]; decide), P.hg.slot ok hn (by rw [P.hg.F]; decide),
    Geo.sep (by oomega) (by oomega) hn, Geo.sep (by oomega) (by oomega) hn,
    P.hg.slot ok hn (by rw [P.hg.F]; decide), P.hg.slot ok hn (by rw [P.hg.F]; decide)⟩

theorem away_low : Away L scr so sl dOff dl L.LOW := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  exact ⟨Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega_arith),
    Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega_arith), P.hg.low ok (by oomega),
    P.hg.low ok (by oomega), Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega_arith),
    Lay.fr_low (by decide) (by have := ok.B56; have := L.B.isLt; omega_arith)⟩

/-- So does a slot other than theirs. -/
theorem away_slot {d : Nat} (hd : d + 4 ≤ frameBytes) (h₁ : d + 4 ≤ sCtr ∨ sDone + 4 ≤ d)
    (h₂ : d + 4 ≤ sTab ∨ sHl + 4 ≤ d) : Away L scr so sl dOff dl (slotR L d) := by
  have := P.fs; have := P.fd
  obtain ⟨σ', ok⟩ := P.hg.ok
  have hF : d + 4 ≤ L.F + 56 := by rw [P.hg.F]; unfold frameBytes at hd ⊢; omega_arith
  refine ⟨slotSep (by decide) hd (by unfold sCtr sDone at *; omega_arith),
    slotSep (by decide) hd (by unfold sCtr sDone at *; omega_arith), (P.hg.slot ok (by oomega) hF).symm,
    (P.hg.slot ok (by oomega) hF).symm, slotSep (by decide) hd (by unfold sTab sHl at *; omega_arith),
    slotSep (by decide) hd (by unfold sTab sHl at *; omega_arith)⟩

end MP

/-- The counter's bytes at `oCtr`. -/
abbrev Cb (scr : BitVec 32) (c : Nat) (m : Mem) : Prop := ∀ i < 4, m (sa scr (oCtr + i)) = (Spec.Rsa.i2osp c 4).getD i 0

/-- The digest of `src ‖ C` at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < g.H.D, m (sa scr (oDig + i)) = (g.ok.SH.H.hash x).getD i 0

/-- The memory after the XOR of iteration `c`. -/
structure DX (L : Lay) (scr : BitVec 32) (so sl dOff dl c : Nat) (dstv : Nat → Byte) (seed : List Byte) (m : Mem) :
    Prop where
  tabS : m.readW (L.fr sTab) 32 = L.argv.getD j 0
  hlS : m.readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D
  ctr : m.readW (L.fr sCtr) 32 = BitVec.ofNat 32 c
  done : m.readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D)
  dx : ∀ i < dl, m (sa scr (dOff + i)) =
    if i < c * g.H.D + g.H.D then dstv i ^^^ (Spec.Mgf1.mgf1 g.G seed dl).getD i 0 else dstv i
  sd : ∀ i < sl, m (sa scr (so + i)) = seed.getD i 0

/-! ## A call through the table -/

/-- `ldr r, [r, #o]` of the table's word at `p + o`. -/
theorem wp_ldrT {s : State} {r : Reg} {p a : BitVec 32} {o : Nat} (ho : o < 4096) (hr : s.gpr r = p)
    (hin : InRegions (s.rd ++ s.wr) (tA p o) 4) (hv : s.mem.readW (tA p o) 32 = a) :
    WP isa (.block [.ldr r r o]) s fun t => t = s.setReg r a := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, ho, ↓reduceIte, hr, State.load32, hin, hv, Option.map_some, runStep_some,
    runBlock_nil]
  simp

/-- `ldr r, [sp, #d]` of a slot. -/
theorem wp_ldS (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (ho : d < 4096) : WP isa (.block [.ldrSp r d]) s fun t => t = s.setReg r (s.mem.readW (L.fr d) 32) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, ho, ↓reduceIte, State.load32, hc.st.sp, hc.aFr hg d hd, hc.rFr hg d hd,
    Option.map_some, runStep_some, runBlock_nil]
  simp

section TCall

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af) (c : Nat)
include P

/-- The table's word `k`, `a` in every run, into `r4`, from a stage with
`Ctx`, MGF1's memory before iteration `c` and `X`, which a write of `r4`
keeps. -/
theorem tload_vp {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v)) {k : Nat}
    (hk3 : k < 3) {a : BitVec 32}
    (ha : ∀ σ, TabFacts g.H f (L.argv.getD j 0) ai au af σ → σ.mem.readW (tA (L.argv.getD j 0) (4 * k)) 32 = a) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
        s.syms = σ.syms) (.block (tload k))
      (fun σ s => ((Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
        s.syms = σ.syms) ∧ s.gpr .r4 = a) := by
  have hg := P.hg
  have hk : 4 * k + 4 ≤ 20 := by omega
  obtain ⟨tR, tRo, tC⟩ := P.tbl
  let F : State → State → Prop := fun σ s =>
    (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧ s.syms = σ.syms
  have keepF : ∀ σ s v, F σ s → F σ (s.setReg .r4 v) := fun σ s v ⟨⟨hc, hm, hx⟩, sy⟩ =>
    ⟨⟨Ctx.setReg_iff.mpr hc, hm, hX σ s v hx⟩, sy⟩
  show VP F (.block ([Impl.RsaPss.Arm.ld .r4 sTab] ++ [.ldr .r4 .r4 (4 * k)])) (fun σ s => F σ s ∧ s.gpr .r4 = a)
  refine VP.block_append (G := fun σ s => F σ s ∧ s.gpr .r4 = L.argv.getD j 0)
    (VP.ldrSp (c := [(.r4, sTab)]) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm)
      fun σ s hs => WP.mono (wp_ldS hg hs.1.1 (r := .r4) (by decide) (by decide)) fun t e => ?_)
    (VP.taint [.r4] (tword_cert hk3) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · subst e
    exact ⟨keepF σ s _ hs, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]; exact hs.1.2.1.2.tabS⟩
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  · obtain ⟨hF, hsi⟩ := hs
    have T := P.tab σ _ hF.1.2.1.1
    refine WP.mono (wp_ldrT (by omega) hsi (St_roR hF.1.1.st tRo (tC _ hk))
      ((St_roW hF.1.1.st tRo (tC _ hk)).trans (ha σ T))) fun t e => ?_
    subst e
    exact ⟨keepF σ s _ hF, by simp only [VG.Arm.RegUpd.gpr_setReg, ↓reduceIte]⟩

/-- The call of `init` through the table, as the call of `g`'s. -/
theorem tcallI_vp {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
      s.syms = σ.syms) (.call g.H.initN g.H.initC) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
      s.syms = σ.syms) (callInit f) G :=
  tcall_vp P.fne.1 (tload_vp P c hX (k := 0) (by decide) (a := ai) fun σ T => T.mem.1.trans T.ai)
    (fun σ s ⟨⟨_, sy⟩, hsi⟩ => by
      have T := P.tab σ _ (‹Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s›).2.1.1
      show f.init.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .r4).setWidth 64) = _
      rw [hsi, sy, ← T.ai]; exact T.ok.i)
    (fun _ _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (h.mono (fun _ _ hh => hh.1) fun _ _ hh => hh)

/-- The call of the table's function `k`, among `ts`, in a frame pushing
`rs`, as the call of `n`, at `a` in every run, in that frame. -/
theorem tcallK_vp {X : State → State → Prop} (hX : ∀ σ s v, X σ s → X σ (s.setReg .r4 v)) {k : Nat}
    (hk3 : k < 3) {ts : List (String × Prog isa)} {rs : List Reg} {m : Nat} {n : String} {cn : Prog isa}
    {a : BitVec 32} (hne : ts ≠ [])
    (ha : ∀ σ, TabFacts g.H f (L.argv.getD j 0) ai au af σ →
      σ.mem.readW (tA (L.argv.getD j 0) (4 * k)) 32 = a ∧ σ.syms n = a ∧
        ts.find? (fun q => (σ.syms q.1).setWidth 64 == (σ.syms n).setWidth 64) = some (n, cn))
    {G : State → State → Prop}
    (h : VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
      s.syms = σ.syms) (.frame (.push rs) (.call n cn) (.pop .r1 m)) G) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧ X σ s) ∧
      s.syms = σ.syms) (tcallF k ts rs m) G :=
  tcallF_vp hne (tload_vp P c hX hk3 (a := a) fun σ T => (ha σ T).1)
    (fun σ s ⟨⟨hF, sy⟩, hsi⟩ => by
      have T := P.tab σ _ hF.2.1.1
      obtain ⟨-, hn, hf⟩ := ha σ T
      show ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.gpr .r4).setWidth 64) = _
      rw [hsi, sy, ← hn]; exact hf)
    (fun _ _ _ _ h₁ h₂ => ⟨h₁.2.trans h₂.2.symm, h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm⟩)
    (h.mono (fun _ _ hh => hh.1) fun _ _ hh => hh)

end TCall

/-! ## The stages of an iteration -/

section Iter

variable {g} (P : MP g L scr so sl dOff dl seed Inv f j ai au af) (c : Nat)
include P

/-- The state set to the empty message, through the table. -/
theorem mgfA_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
      (.seq (.block initArgs) (callInit f))
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) []) ∧ s.syms = σ.syms) := by
  have := g.S_le
  have hI : ∀ σ m m', MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m → Frame [sR scr oSt g.H.S, L.LOW] m m' →
      MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m' := fun σ m m' hm hf =>
    P.keep hm hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact P.away_hi (by oomega) (by oomega)
      · exact P.away_low
  refine VP.seq (VP.syms (initArgs_vp P.hg)) ?_
  exact tcallI_vp P c (X := fun _ s => s.gpr .r0 = scr + BitVec.ofNat 32 oSt)
    (fun _ _ _ h => by simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h)
    ((VP.syms (initCall_vp P.hg g.H g.ok hI)).mono (fun σ s ⟨⟨hc, hm, hb⟩, sy⟩ => ⟨⟨hc, hm, hb⟩, sy⟩)
      fun _ _ h => h)

/-- `update(state, 0, src, sl, work)`'s arguments. -/
theorem mgfB_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [])
      (.block updSrcArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) := by
  have hg := P.hg
  have := P.fs
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_
  have hw : WP isa (.block updSrcArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      UArgs scr (scr + BitVec.ofNat 32 so) sl 0 t := by
    prun [updSrcArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.src σ _ hm.1, P.srcL σ _ hm.1,
      sSrc_lt, sSrcLen_lt, movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ => ⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp, rfl, ?_, u⟩
  rw [m]; exact bytesAt_scr hg (by oomega) (P.sd σ) hm.2.sd

/-- `update` absorbs `src`. -/
theorem mgfC_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
      (updCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aS : State.addr (scr + BitVec.ofNat 32 so) = sa scr so := hg.addr (by have := P.sl0; oomega)
  refine upd_vp hg g.H g.ok (msg := fun _ => []) (dat := seed) (c := 0) (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv)
    (hg.rbuf (o := so) (n := sl) (by oomega) P.sl0)
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aS]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aS]; exact hg.low ok (by oomega))
    (by decide) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low

/-- `update` absorbs `src`, through the table. -/
theorem mgfC_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
        UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s) ∧ s.syms = σ.syms)
      (callUpd f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) [] ∧ ([] : List Byte).length = 0 ∧
      Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 so)) sl = seed σ ∧
      UArgs scr (scr + BitVec.ofNat 32 so) sl 0 s)
    (fun _ _ v ⟨r, l, b, ua⟩ => ⟨r, l, b, ua.r4 v⟩) (k := 1) (by decide) P.fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩) (VP.syms (mgfC_call P c))

/-- The counter, big-endian, at `oCtr`. -/
theorem mgfD_vp (hc32 : c < 2 ^ 32) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ))
      (.seq (.block ctrSet) (.block ctrPut))
      (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le
  obtain ⟨σ', ok⟩ := hg.ok
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
      g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 oCtr ∧ s.gpr .r1 = BitVec.ofNat 32 c)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_)
    (VP.taint _ ctrPut_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, ⟨hm, rp⟩, r0, r1⟩ => ?_)
  · have hw : WP isa (.block ctrSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oCtr ∧ t.gpr .r1 = BitVec.ofNat 32 c := by
      prun [ctrSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hm.2.ctr,
        movw_val (show oCtr < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨hc.regs rd wr sp m, ⟨m ▸ hm, m ▸ rp⟩, r0, r1⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · have a0 : State.addr (scr + BitVec.ofNat 32 oCtr) = sa scr oCtr := hg.addr (by oomega)
    have aj : ∀ j, j < 4 → State.addr (scr + BitVec.ofNat 32 (oCtr + j)) = sa scr (oCtr + j) :=
      fun j hj => hg.addr (by oomega)
    have wj : ∀ j, j < 4 → InRegions s.wr (sa scr (oCtr + j)) 1 := fun j hj => hg.wr hc.st (by oomega)
    have w0 : InRegions s.wr (sa scr oCtr) 1 := hg.wr hc.st (by oomega)
    have hw : WP isa (.block ctrPut) s fun t =>
        t.mem = (((s.mem.writeW (sa scr oCtr) (BitVec.ofNat 8 (c / 256 ^ 3))).writeW (sa scr (oCtr + 1))
          (BitVec.ofNat 8 (c / 256 ^ 2))).writeW (sa scr (oCtr + 2)) (BitVec.ofNat 8 (c / 256 ^ 1))).writeW
            (sa scr (oCtr + 3)) (BitVec.ofNat 8 (c / 256 ^ 0)) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [ctrPut, r0, r1, a0, aj 1 (by decide), aj 2 (by decide), aj 3 (by decide), w0, wj 1 (by decide),
        wj 2 (by decide), wj 3 (by decide), shrByte hc32 3, shrByte hc32 2, shrByte hc32 1, shr0 c,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    have fr : Frame [sR scr oCtr 4] s.mem t.mem := by
      rw [m]
      refine (((frame_byte scr _ _ ?_ ?_ ?_).trans (frame_byte scr _ _ ?_ ?_ ?_)).trans
        (frame_byte scr _ _ ?_ ?_ ?_)).trans (frame_byte scr _ _ ?_ ?_ ?_) <;> oomega
    refine ⟨ctxW hg hc fr (fun r hr => .inl ⟨oCtr, 4, by oomega, by simpa using hr⟩) rd wr sp,
      ⟨P.keep hm fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact P.away_hi (by oomega) (by oomega),
        g.ok.repr _ _ _ _ _ (fun i hi => ?_) rp⟩, fun i hi => ?_⟩
    · exact fr.bytes (R := sR scr oSt g.H.S) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by oomega) (by oomega) (by oomega))
        (by show g.H.S ≤ 2 ^ 64; omega_arith) hi
    rw [m, sa_write scr _ _ (o := oCtr + 3) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr + 2) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr + 1) (i := oCtr + i) (by oomega) (by oomega),
      sa_write scr _ _ (o := oCtr) (i := oCtr + i) (by oomega) (by oomega), i2osp4_getD c _ hi]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_arith
    rcases this with rfl | rfl | rfl | rfl <;>
      simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right, Nat.reduceSub]

/-- `update(state, sl, scratch + oCtr, 4, work)`'s arguments. -/
theorem mgfE_vp :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ)) ∧ Cb scr c s.mem)
      (.block updCtrArgs)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) := by
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, ⟨hm, rp⟩, cb⟩ => ?_
  have hw : WP isa (.block updCtrArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl t := by
    prun [updCtrArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.srcL σ _ hm.1, sSrcLen_lt,
      movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
      movw_val (show oCtr < 2 ^ 16 by decide), movw_val (show 4 < 2 ^ 16 by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine WP.mono hw fun t ⟨m, rd, wr, sp, u⟩ => ⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp,
    by rw [List.nil_append, P.sd σ], ?_, u⟩
  rw [m]; exact bytesAt_scr hg (by oomega) (i2osp4_length c) cb

/-- `update` absorbs the counter. -/
theorem mgfF_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
      (updCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le
  obtain ⟨σ', ok⟩ := hg.ok
  have aC : State.addr (scr + BitVec.ofNat 32 oCtr) = sa scr oCtr := hg.addr (by oomega)
  refine upd_vp hg g.H g.ok (msg := fun σ => [] ++ seed σ) (dat := fun _ => Spec.Rsa.i2osp c 4) (c := sl)
    (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv) (hg.rbuf (o := oCtr) (n := 4) (by oomega) (by decide))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega))
    (by rw [aC]; exact Geo.sep (by oomega) (by oomega) (by oomega)) (by rw [aC]; exact hg.low ok (by oomega))
    (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low

/-- `update` absorbs the counter, through the table. -/
theorem mgfF_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
        Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
        UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s) ∧ s.syms = σ.syms)
      (callUpd f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ) ∧ ([] ++ seed σ).length = sl ∧
      Spec.Sha256.bytesAt s.mem (State.addr (scr + BitVec.ofNat 32 oCtr)) 4 = Spec.Rsa.i2osp c 4 ∧
      UArgs scr (scr + BitVec.ofNat 32 oCtr) 4 sl s)
    (fun _ _ v ⟨r, l, b, ua⟩ => ⟨r, l, b, ua.r4 v⟩) (k := 1) (by decide) P.fne.2.1 (a := au)
    (fun σ T => ⟨T.mem.2.1.trans T.au, T.au, T.ok.u⟩) (VP.syms (mgfF_call P c))

/-- `finalize(state, sl + 4, scratch + oDig, work)`'s arguments, the working
space moved to `r12`. -/
theorem mgfG_vp :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4))
      (.seq (.block finArgs) (.block toR12))
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) := by
  have hg := P.hg
  have := P.fs
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
      g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4)) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
      s.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ s.gpr .r2 = BitVec.ofNat 32 (sl + 4) ∧ s.gpr .r3 = 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, rp⟩ => ?_)
    ((toR12_vp (fun σ s h => h.2.2.2.1) fun σ s v h => ?_).mono
      (fun _ _ h => h) fun σ s ⟨⟨⟨hc, hm, rp⟩, r0, r1, _, r2, r3⟩, r12⟩ => ⟨hc, hm, rp,
        by rw [List.length_append, List.nil_append, P.sd σ, i2osp4_length], r0, r1, r12, r2, r3⟩)
  · have e4 : BitVec.ofNat 32 sl + 4 = BitVec.ofNat 32 (sl + 4) := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.ofNat_add_ofNat]
    have hw : WP isa (.block finArgs) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        t.gpr .r10 = scr + BitVec.ofNat 32 oW ∧ t.gpr .r2 = BitVec.ofNat 32 (sl + 4) ∧ t.gpr .r3 = 0 := by
      prun [finArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.srcL σ _ hm.1, sSrcLen_lt,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oW < 2 ^ 16 by decide),
        movw_val (show oDig < 2 ^ 16 by decide), BitVec.ofNat_add_ofNat, dpVal, e4]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, r10, r2, r3⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hm, m ▸ rp⟩, r0, r1, r10,
      r2, r3⟩
  · obtain ⟨⟨hc, hm, rp⟩, r0, r1, r10, r2, r3⟩ := h
    have e : ∀ r, r ≠ .r12 → (s.setReg .r12 v).gpr r = s.gpr r := fun r hr => by
      simp only [VG.Arm.RegUpd.gpr_setReg, hr, ite_false]
    exact ⟨⟨Ctx.setReg_iff.mpr hc, hm, rp⟩, by rw [e _ (by decide), r0], by rw [e _ (by decide), r1],
      by rw [e _ (by decide), r10], by rw [e _ (by decide), r2], by rw [e _ (by decide), r3]⟩

/-- `finalize` writes the digest. -/
theorem mgfH_call :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
      (finCall g.H)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) := by
  have hg := P.hg
  have := P.fs; have := g.S_le; have := g.Wb_le; have := g.F_le; have := g.DF
  refine (fin_vp hg g.H g.ok (o := oDig) (c := sl + 4) (msg := fun σ => [] ++ seed σ ++ Spec.Rsa.i2osp c 4)
    (Inv := MI g (j := j) L scr so sl dOff dl c dstv seed Inv)
    (.inr (by oomega)) (.inl (by oomega)) (by oomega) (by oomega) fun σ m m' hm hf => P.keep hm hf (fun r hr => ?_) fun r hr => ?_).mono
    (fun _ _ h => h) fun σ s ⟨hc, hm, hd⟩ => ⟨hc, hm, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_hi (by oomega) (by oomega)
    · exact P.away_low
  · have e := congrArg (fun l => l.getD i 0) hd
    simp only [List.nil_append] at e
    rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, Spec.Sha256.bytesAt,
      List.getElem?_map, List.getElem?_range (by omega_arith)]
    simp only [Option.map_some, Option.getD_some, sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- `finalize` writes the digest, through the table. -/
theorem mgfH_vp :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
        ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s) ∧ s.syms = σ.syms)
      (callFin f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧ s.syms = σ.syms) :=
  tcallK_vp P c (X := fun σ s => g.ok.SH.Repr s.mem (sa scr oSt) ([] ++ seed σ ++ Spec.Rsa.i2osp c 4) ∧
      ([] ++ seed σ ++ Spec.Rsa.i2osp c 4).length = sl + 4 ∧ FArgs scr oDig (sl + 4) s)
    (fun _ _ v ⟨r, l, fa⟩ => ⟨r, l, fa.r4 v⟩) (k := 2) (by decide) P.fne.2.2 (a := af)
    (fun σ T => ⟨T.mem.2.2.trans T.af, T.af, T.ok.f⟩) (VP.syms (mgfH_call P c))

/-- The XOR's registers. -/
theorem mgfI_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem)
      (.block xorSet)
      (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D))) := by
  have hD := g.D_le
  have hfd := P.fd
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hm, hd⟩ => ?_
  have hw : WP isa (.block xorSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧
      t.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
      t.gpr .lr = if dl - c * g.H.D < g.H.D then BitVec.ofNat 32 (dl - c * g.H.D) else BitVec.ofNat 32 g.H.D := by
    prun [xorSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, P.dst σ _ hm.1,
      P.dstL σ _ hm.1, hm.2.done, hm.2.hlS, sDst_lt, sDstLen_lt, sHl_lt, movw_val (show oDig < 2 ^ 16 by decide),
      BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Offset.ofNat_sub_ofNat (w := 32) (show c * g.H.D ≤ dl by omega_arith),
      ltBit (a := dl - c * g.H.D) (b := g.H.D) (by oomega) (by omega_arith), neg_bit, neg_bit', selW, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hm, hd⟩, r0, r1, ?_⟩
  rw [lr]
  split
  · rw [Nat.min_eq_right (by omega_arith)]
  · rw [Nat.min_eq_left (by omega_arith)]

/-- The XOR of the digest into `dst`. -/
theorem mgfJ_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ (MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem ∧
        Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) s.mem) ∧
        s.gpr .r0 = scr + BitVec.ofNat 32 (dOff + c * g.H.D) ∧ s.gpr .r1 = scr + BitVec.ofNat 32 oDig ∧
        s.gpr .lr = BitVec.ofNat 32 (min g.H.D (dl - c * g.H.D)))
      (countLoop xorBody)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) s.mem) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hn : min g.H.D (dl - c * g.H.D) = n
  have hn0 : 0 < n := by omega_arith
  have hnD : n ≤ g.H.D := by omega_arith
  have hnd : c * g.H.D + n ≤ dl := by omega_arith
  refine (xor_vp hg (od := dOff + c * g.H.D) (os := oDig) (n := n) hn0 (by oomega) (by oomega) (by oomega)
    (X := fun σ m => MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ m ∧ Dg g scr (seed σ ++ Spec.Rsa.i2osp c 4) m)).mono
    (fun _ _ h => h) fun σ s ⟨hc, m₀, ⟨hm, hd⟩, hf, hx⟩ => ⟨hc, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · refine P.I σ _ _ hm.1 (Frame.sub hf fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sR scr dOff dl, by simp, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.tabS
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.hlS
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.ctr
  · exact slot_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by oomega) (by rw [hg.F]; decide)) hm.2.done
  · have old := hm.2.dx i hi
    by_cases h1 : i < c * g.H.D
    · rw [ite_eq_left (by omega_arith)]
      rw [ite_eq_left h1] at old
      rw [← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
    rw [ite_eq_right h1] at old
    by_cases h2 : i < c * g.H.D + n
    · rw [ite_eq_left (by omega_arith), g.mask_byte (c := c) hi (by omega_arith) (by omega_arith), ← hd _ (by omega_arith), ← old]
      have e := hx (i - c * g.H.D) (by omega_arith)
      rw [show dOff + c * g.H.D + (i - c * g.H.D) = dOff + i by omega_arith] at e
      exact e
    · rw [ite_eq_right (by omega_arith), ← old]
      exact hf _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Geo.sep (scr := scr) (o := dOff + i) (n := 1) (by oomega) (by oomega) (by oomega) _
          (Region.contains_self _ _)
  · exact sbytes_keep hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases P.sep with h | h
      · exact Geo.sep (by oomega) (by oomega) (by oomega)
      · exact Geo.sep (by oomega) (by oomega) (by oomega)) (by oomega) hm.2.sd

/-- The next counter and bytes masked. -/
theorem mgfK_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ DX g (j := j) L scr so sl dOff dl c (dstv σ) (seed σ) s.mem)
      (.block mgfNext)
      (fun σ s => Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.z = decide (dl ≤ c * g.H.D + g.H.D)) := by
  have hD := g.D_le
  have hfd := P.fd
  have hfs := P.fs
  have hg := P.hg
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, hm⟩ => ?_
  have r1 : ∀ v : BitVec 32, (s.mem.writeW (L.fr sCtr) v).readW (L.fr sDone) 32 = BitVec.ofNat 32 (c * g.H.D) :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide), hm.done]
  have r2 : ∀ v w : BitVec 32, ((s.mem.writeW (L.fr sCtr) v).writeW (L.fr sDone) w).readW (L.fr sDstLen) 32 =
      BitVec.ofNat 32 dl :=
    fun v w => by rw [slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      P.dstL σ _ hi]
  have rH : ∀ v : BitVec 32, (s.mem.writeW (L.fr sCtr) v).readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D :=
    fun v => by rw [slot_ww _ _ (by decide) (by decide) (by decide), hm.hlS]
  have hw : WP isa (.block mgfNext) s fun t =>
      t.mem = (s.mem.writeW (L.fr sCtr) (BitVec.ofNat 32 (c + 1))).writeW (L.fr sDone)
        (BitVec.ofNat 32 (c * g.H.D + g.H.D)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (dl ≤ c * g.H.D + g.H.D) := by
    prun [mgfNext, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hm.ctr, r1, r2, rH, sDstLen_lt,
      sHl_lt, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32,
      BitVec.ofNat_add_ofNat, ltBit (a := c * g.H.D + g.H.D) (b := dl) (by oomega) (by oomega), bit_z, dpVal]
    simp only [decide_eq_decide]
    omega_arith
  refine WP.mono hw fun t ⟨m, rd, wr, sp, z⟩ => ?_
  have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
    rw [m]
    exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  have dis : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
    intro r hr o n hon
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, z⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotW hg (by decide)
    · exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact slotSep (by decide) (by decide) (by decide)
    · exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide), hm.tabS]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide), hm.hlS]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32, Nat.succ_mul]
  · intro i hi'
    rw [Nat.succ_mul]
    exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.dx i hi'
  · exact sbytes_keep fr (fun r hr => dis r hr _ _ (by oomega)) (by oomega) hm.sd

/-- An iteration of `mgfXor`. -/
theorem mgfIter_vp (hcd : c * g.H.D < dl) :
    VP (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl c dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
      (mgfRound f)
      (fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl (c + 1) dstv seed Inv σ s.mem ∧
        s.z = decide (dl ≤ c * g.H.D + g.H.D)) ∧ s.syms = σ.syms) := by
  have hc32 : c < 2 ^ 32 := by
    have := P.fd
    have : c ≤ c * g.H.D := Nat.le_mul_of_pos_right c g.D_pos
    oomega
  show VP _ (.seq (.block initArgs) (.seq (callInit f) (.seq (.block updSrcArgs) (.seq (callUpd f)
    (.seq (.block ctrSet) (.seq (.block ctrPut) (.seq (.block updCtrArgs) (.seq (callUpd f) (.seq (.block finArgs)
      (.seq (.block toR12) (.seq (callFin f) (.seq (.block xorSet) (.seq (countLoop xorBody)
        (.block mgfNext)))))))))))))) _
  exact VP.assoc (VP.seq (mgfA_vp P c) (VP.seq (VP.syms (mgfB_vp P c)) (VP.seq (mgfC_vp P c)
    (VP.assoc (VP.seq (VP.syms (mgfD_vp P c hc32)) (VP.seq (VP.syms (mgfE_vp P c)) (VP.seq (mgfF_vp P c)
      (VP.assoc (VP.seq (VP.syms (mgfG_vp P c)) (VP.seq (mgfH_vp P c) (VP.seq (VP.syms (mgfI_vp P c hcd))
        (VP.seq (VP.syms (mgfJ_vp P c hcd)) (VP.syms (mgfK_vp P c hcd))))))))))))))

end Iter

/-- The table that is our argument `j` to its slot. -/
theorem tabA_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) (hj : j < L.argv.length)
    (hoff : Impl.RsaPss.Arm.arg j < 4096) :
    WP isa (.block [sp0, ld .r0 (Impl.RsaPss.Arm.arg j), st .r0 sTab]) s fun t =>
      t.mem = s.mem.writeW (L.fr sTab) (L.argv.getD j 0) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = L.argv.getD j 0 ∧ t.gpr .r12 = L.B ∧ t.syms = s.syms := by
  have hn := hc.st.ok.nargs
  have ha := Lay.argOff_lt (L := L) (j := j) (by omega)
  have hA : State.addr (L.B + BitVec.ofNat 32 (Impl.RsaPss.Arm.arg j)) = L.argA j := by
    show State.addr (L.B + BitVec.ofNat 32 (Impl.RsaPkcs1Sig.Arm.argOff frameBytes j)) = _
    rw [← hg.F]; exact hc.st.ok.addrB (by omega)
  have hR : InRegions (s.rd ++ s.wr) (L.argA j) 4 := by rw [hc.st.rd, hc.st.wr]; exact hc.st.ok.arg_read hj
  have hV := hc.st.arg hj
  prun [sp0, ld, st, hc.st.sp, hc.aFr hg, hc.wFr hg, hA, hR, hV, hoff, sTab_lt]
  rfl

/-- The table's digest length (its word 4) to its slot. -/
theorem tabB_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) {p : BitVec 32} {D : BitVec 32}
    (h0 : s.gpr .r0 = p) (h12 : s.gpr .r12 = L.B) (hin : InRegions (s.rd ++ s.wr) (tA p 16) 4)
    (hv : s.mem.readW (tA p 16) 32 = D) :
    WP isa (.block [.ldr .r0 .r0 16, st .r0 sHl]) s fun t =>
      t.mem = s.mem.writeW (L.fr sHl) D ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
  prun [st, h0, h12, hc.aFr hg, hc.wFr hg, State.load32, hin, hv, sHl_lt]
  rfl

/-- `dst ⊕= MGF1(src, dl)`. -/
theorem mgf_vp (P : MP g L scr so sl dOff dl seed Inv f j ai au af) (hoff : Impl.RsaPss.Arm.arg j < 4096) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧ s.syms = σ.syms)
      (mgfXor f j)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i ^^^ (Spec.Mgf1.mgf1 g.G (seed σ) dl).getD i 0) ∧
        ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧ s.syms = σ.syms) := by
  have hD := g.D_le
  have hD0 := g.D_pos
  have hfd := P.fd
  have hfs := P.fs
  have hdl := P.dl0
  have hg := P.hg
  obtain ⟨σ', ok⟩ := hg.ok
  generalize hK : (dl + g.H.D - 1) / g.H.D = K
  have hK0 : 0 < K := by
    rw [← hK]; exact (Nat.le_div_iff_mul_le hD0).2 (by omega_arith)
  have dis : ∀ d, d + 4 ≤ frameBytes → ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint (slotR L d) :=
    fun d hd o n hon => (hg.slot ok hon (by rw [hg.F]; omega_arith)).symm
  let p := L.argv.getD j 0
  let F0 : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
    (∀ i < dl, s.mem (sa scr (dOff + i)) = dstv σ i) ∧ ∀ i < sl, s.mem (sa scr (so + i)) = (seed σ).getD i 0) ∧
    s.syms = σ.syms
  show VP F0 (.seq (.block ([sp0, ld .r0 (Impl.RsaPss.Arm.arg j), st .r0 sTab] ++
    ([.ldr .r0 .r0 16, st .r0 sHl] ++ mgfInit))) (.loop (mgfRound f) .ne)) _
  refine VP.seq (G := fun σ s => (Ctx L scr σ s ∧ MI g (j := j) L scr so sl dOff dl 0 dstv seed Inv σ s.mem) ∧
    s.syms = σ.syms) (VP.block_append (G := fun σ s => F0 σ s ∧ s.mem.readW (L.fr sTab) 32 = p ∧
      s.gpr .r0 = p ∧ s.gpr .r12 = L.B)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s hs => ?_)
    (VP.block_append (G := fun σ s => F0 σ s ∧ s.mem.readW (L.fr sTab) 32 = p ∧
        s.mem.readW (L.fr sHl) 32 = BitVec.ofNat 32 g.H.D)
      (VP.taint [.r0, .r12] tabD_cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm) fun σ s hs => ?_))) ?_
  · obtain ⟨⟨hc, hi, hd, hs⟩, sy⟩ := hs
    refine WP.mono (tabA_wp hg hc P.hj hoff) fun t ⟨m, rd, wr, sp, r0, r12, ty⟩ => ?_
    have fr : Frame [slotR L sTab] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    refine ⟨⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, P.I σ _ _ hi (fr.mono (by simp)),
      fun i hi' => ?_, ?_⟩, ty.trans sy⟩, by rw [m, Mem.readW_writeW_self32], r0, r12⟩
    · rw [List.mem_singleton.mp hr]; exact slotW hg (by decide)
    · rw [List.mem_singleton.mp hr]; exact slotSep (by decide) (by decide) (by decide)
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
  · obtain ⟨⟨⟨hc, hi, hd, hs⟩, sy⟩, ht, h0, h12⟩ := hs
    have T := P.tab σ _ hi
    obtain ⟨tR, tRo, tC⟩ := P.tbl
    refine WP.mono (tabB_wp hg hc h0 h12 (St_roR hc.st tRo (tC 16 (by decide)))
      ((St_roW hc.st tRo (tC 16 (by decide))).trans T.d)) fun t ⟨m, rd, wr, sp, ty⟩ => ?_
    have fr : Frame [slotR L sHl] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    refine ⟨⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, P.I σ _ _ hi (fr.mono (by simp)),
      fun i hi' => ?_, ?_⟩, ty.trans sy⟩, ?_, by rw [m, Mem.readW_writeW_self32]⟩
    · rw [List.mem_singleton.mp hr]; exact slotW hg (by decide)
    · rw [List.mem_singleton.mp hr]; exact slotSep (by decide) (by decide) (by decide)
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => by rw [List.mem_singleton.mp hr]; exact dis _ (by decide) _ _ (by oomega))
        (by oomega) hs
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), ht]
  · obtain ⟨⟨⟨hc, hi, hd, hs⟩, sy⟩, ht, hh⟩ := hs
    have hw : WP isa (.block mgfInit) s fun t =>
        t.mem = (s.mem.writeW (L.fr sCtr) (0 : BitVec 32)).writeW (L.fr sDone) (0 : BitVec 32) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.syms = s.syms := by
      prun [mgfInit, sp0, st, mw, hc.st.sp, hc.aFr hg, hc.wFr hg]
      rfl
    refine WP.mono hw fun t ⟨m, rd, wr, sp, ty⟩ => ?_
    have fr : Frame [slotR L sCtr, slotR L sDone] s.mem t.mem := by
      rw [m]
      exact (slot_frame L _ _ _).mono (by simp) |>.trans ((slot_frame L _ _ _).mono (by simp))
    have dis2 : ∀ r ∈ [slotR L sCtr, slotR L sDone], ∀ o n, o + n ≤ oRsa → (sR scr o n).Disjoint r := by
      intro r hr o n hon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
      · exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      P.I σ _ _ hi (fr.mono (by simp)), ⟨?_, ?_, ?_, ?_, fun i hi' => ?_, ?_⟩⟩, ty.trans sy⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotW hg (by decide)
      · exact slotW hg (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotSep (by decide) (by decide) (by decide)
      · exact slotSep (by decide) (by decide) (by decide)
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide), ht]
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide), hh]
    · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
    · rw [m, Mem.readW_writeW_self32, Nat.zero_mul]; rfl
    · rw [ite_eq_right (by omega_arith)]
      exact sbytes_keep fr (fun r hr => dis2 r hr _ _ (by oomega)) (by oomega) hd i hi'
    · exact sbytes_keep fr (fun r hr => dis2 r hr _ _ (by oomega)) (by oomega) hs
  refine (VP.loop (I := fun k σ s => k ≤ K ∧ (Ctx L scr σ s ∧
      MI g (j := j) L scr so sl dOff dl (K - k) dstv seed Inv σ s.mem) ∧ s.syms = σ.syms)
    (fun k => ?_) (K - 1)).mono (fun σ s hs => ⟨by omega_arith, by rw [show K - (K - 1 + 1) = 0 by omega_arith]; exact hs⟩)
    fun _ _ h => h
  by_cases hk : k + 1 ≤ K
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hk h
  generalize hc : K - (k + 1) = c
  have key : ∀ x, (dl + g.H.D - 1) / g.H.D ≤ x + 1 ↔ dl ≤ x * g.H.D + g.H.D := fun x => by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hD0, Nat.succ_mul, Nat.succ_mul]
    omega_arith
  have hcd : c * g.H.D < dl := by
    have := (Nat.le_div_iff_mul_le hD0).1 (show c + 1 ≤ (dl + g.H.D - 1) / g.H.D by omega_arith)
    rw [Nat.succ_mul] at this
    omega_arith
  refine (mgfIter_vp P c hcd).mono (fun σ s ⟨_, hs⟩ => hs) fun σ s ⟨⟨hc', hm, z⟩, sy⟩ =>
    ⟨?_, fun h0 => ?_, fun hp => ?_⟩
  · rw [VG.Proof.X25519.Arm.eval_ne, z]
    have e := key c
    rw [hK] at e
    by_cases hz : k = 0
    · rw [decide_eq_true (e.1 (by omega_arith)), hz]; rfl
    · rw [decide_eq_false (fun h' => hz (by have := e.2 h'; omega_arith))]
      simp only [Bool.not_false, Option.some.injEq]
      exact (decide_eq_true (by omega_arith)).symm
  · have e := (key c).1 (by omega_arith)
    refine ⟨⟨hc', hm.1, fun i hi => ?_, hm.2.sd⟩, sy⟩
    rw [hm.2.dx i hi, ite_eq_left (by rw [Nat.succ_mul]; omega_arith)]
  · exact ⟨by omega_arith, ⟨hc', by rw [show K - k = c + 1 by omega_arith]; exact hm⟩, sy⟩

end VG.Proof.RsaOaep.Arm
