import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Main
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 public-key derivation on AArch64: `Verified`

Correctness including the ABI (`publicKey_ok`), for any implementation `v`
of the Keccak permutation, given that `vg_ed448_scalar_base` meets
its contract in constant time (`BaseOk`, which the generic file passes in). Constant time: two runs whose pointers agree have the same
layout, so in the frame's body they are related by `Two`: both satisfy `Ctx`
with that layout (and what the next block or call needs of the registers,
`Slots`), whatever their secrets. The blocks address only the stack and
`scratch`, from registers that agree (the taint analysis); each call is of
constant-time code (the sponge functions for `v`, `vg_ed448_scalar_base`)
whose public data, its pointers and lengths, agree (`Whole.callEx`).
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (Value setup callWith)
open VG.Impl.Ed448.AArch64.Whole (zeroStores)
open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)

abbrev Two (L : Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Ctx L g₁ v₁ m₁ a ∧ a.syms combSym = L.T ∧ P a) ∧ (Ctx L g₂ v₂ m₂ b ∧ b.syms combSym = L.T ∧ P b)

/-- The registers hold what `setup args` moves into them. -/
def Slots (L : Lay) (args : List (Reg × Value)) (s : State) := ∀ p ∈ args, s.gpr p.1 = argValue L p.2

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) ht) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ sy => ⟨hc, sy ▸ hy, hs⟩

theorem call_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → t.syms combSym = L.T →
      VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp → a.syms combSym = b.syms combSym →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ ?_ ?_
  · refine VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2.1 (h.1.1.tbl hL ha.2) h.1.2.2
    let rb := ready b h.2.1.sp h.2.2.1 (h.2.1.tbl hL hb.2) h.2.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) (h.1.2.1.trans h.2.2.1.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.2 p hp, h.2.2.2 p hp]
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms ((ready t hc.sp hy (hc.tbl hL ha.2) hs).wpF hc correct hd)
      fun _ hu sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms ((ready t hc.sp hy (hc.tbl hL hb.2) hs).wpF hc correct hd)
      fun _ hu sy => ⟨hu, sy ▸ hy, trivial⟩

/-- A call's arguments, then the call. -/
theorem callWith_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true)
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → t.syms combSym = L.T →
      VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp → a.syms combSym = b.syms combSym →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (callWith (setup args) name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb args hn hv hi hr ht).seq (call_ct hL ha hb correct ct hd ready kp hl)

/-! ## Each block and call -/

def zeroValues : List (Reg × Value) := [(.x15, .caller 2 0)]

theorem zeroStores_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L zeroValues)) (.block zeroStores)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have h15 : ∀ {t : State}, Slots L zeroValues t → t.gpr .x15 = L.scr := fun hs => by
    have h := hs (.x15, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl)
    simp only [argValue, Lay.value, BitVec.add_zero] at h
    exact h
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
      fun r hr => ?_⟩) (by taint_decide)) ?_ ?_
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    rw [h15 h.1.2.2, h15 h.2.2.2]
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, hs⟩
    exact WP.mono_syms (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩
    exact WP.mono_syms (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩
  · intro t ⟨hc, hy, _⟩; exact WP.mono_syms (wipe_step hc hL) fun _ ⟨hu, _⟩ sy => ⟨hu, sy ▸ hy, trivial⟩

def absorb_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L absorbValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.absorbAArch64 L.E L.inputs L.outputs t :=
  ⟨[L.SEED], [ST L, KS L], absorb_pre hL hsp hs, absorb_covers L, sponge_writes L⟩

def pad_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L padValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.padAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, KS L], pad_pre hL hsp hs, covers_writes (sponge_writes L), sponge_writes L⟩

def squeeze_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L squeezeValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.squeezeAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, HS L, KS L], squeeze_pre hL hsp hs, covers_writes (squeeze_writes L), squeeze_writes L⟩

def base_ready (hL : L.Ok) {t : State} (hsy : t.syms combSym = L.T)
    (hm : VG.Proof.Ed448.AArch64.Whole.TblWords L.T t.mem) (hs : Slots L baseValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.scalarBaseLocal L.E L.inputs L.outputs t :=
  ⟨[⟨L.E, 57⟩, L.TB], L.outputs, base_pre hL hs hsy hm, base_covers L, base_writes L⟩

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (ha : Arguments L m₁) (hb' : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.callee)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb' zeroValues
    (by decide) (by simp [zeroValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [zeroValues])
    (by decide) (by taint_decide)
  have a := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_absorb_scratch" ++ v.callee.suffix)
    hL ha hb' (args := absorbValues) (by decide)
    (by simp [absorbValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [absorbValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (Nat.le_of_eq v.absorb_depth) (fun _ hsp _ _ hs => absorb_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .caller 1 0) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 57) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have p := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_pad_scratch" ++ v.callee.suffix)
    hL ha hb' (args := padValues) (by decide)
    (by simp [padValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [padValues])
    (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (Nat.le_of_eq v.pad_depth) (fun _ hsp _ _ hs => pad_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 57) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x4, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 4) rfl), hsp⟩)
    (by decide)
  have q := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (name := "vg_keccak_squeeze_scratch" ++ v.callee.suffix)
    hL ha hb' (args := squeezeValues) (by decide)
    (by simp [squeezeValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt])
    (by simp [squeezeValues]) (by decide) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (Nat.le_of_eq v.squeeze_depth) (fun _ hsp _ _ hs => squeeze_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp _ hg => ⟨hg (.x0, .caller 2 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .const 136) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .const 0) (List.mem_of_getElem? (i := 2) rfl),
      hg (.x3, .frame hashAt) (List.mem_of_getElem? (i := 3) rfl), hg (.x4, .const 114) (List.mem_of_getElem? (i := 4) rfl),
      hg (.x5, .caller 2 keccakScratch) (List.mem_of_getElem? (i := 5) rfl), hsp⟩)
    (by decide)
  have b := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_ed448_scalar_base")
    hL ha hb' (args := baseValues) (by decide)
    (by simp [baseValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [baseValues])
    (by decide) (by taint_decide)
    hb.ok hb.ct
    (VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames base_noFrames) (fun _ _ hy hm hs => base_ready hL hy hm hs)
    (fun _ _ _ _ _ _ hsp hy hg => ⟨hsp, hg (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl),
      hg (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl), hg (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl),
      hy⟩)
    (by decide)
  exact (z.seq (zeroStores_ct.seq (a.seq (p.seq q)))).seq (prune_ct.seq (b.seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, hsy⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, hsy]

theorem publicKey_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKeyWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hb (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_syms hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    have hqs : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).syms combSym = (lay s).T := he ▸ entry_syms hqb
    exact ⟨(body_ct v hb (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_syms hpa, trivial⟩, ⟨hq, hqs, trivial⟩⟩ ea eb).1, trivial⟩

open VG.Proof.X448.AArch64.Base (combWords_length satMem satMem_held)

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
    VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9⟩

theorem sat : ∃ s, (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMem_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem pk_implies : pkLocal.Implies
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, os, oc, sc, ko, ks, kc, no, ns, nc⟩ := h
    refine ⟨?_, hw, os, oc, sc, ko, ks, kc, no, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
      Spec.Ed448.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  sat := sat

theorem publicKey_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    Verified AArch64.target (publicKeyWith v.callee)
      (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v hb h) (publicKey_ct v hb) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed448.AArch64.PublicKey
