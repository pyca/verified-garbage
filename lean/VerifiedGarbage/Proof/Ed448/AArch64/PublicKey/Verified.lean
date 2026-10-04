import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Main
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT

/-!
# Ed448 public-key derivation on AArch64: `Verified`

Correctness including the ABI (`publicKey_ok`), for any implementation `v`
of the Keccak permutation, given `BaseLadderOk` (which the generic file
passes in). Constant time: two runs whose pointers agree have the same
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

abbrev Two (L : Lay) (g₁ g₂ : Reg → Addr) (v₁ v₂ : VReg → BitVec 128) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) := (Ctx L g₁ v₁ m₁ a ∧ P a) ∧ (Ctx L g₂ v₂ m₂ b ∧ P b)

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
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL ha hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (setup_ok hc hL hb hn hv hi hr) fun _ ⟨hc, _, hs⟩ => ⟨hc, hs⟩

theorem call_ct {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L args)) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp ?_ ?_ ?_
  · refine VG.Proof.Ed25519.AArch64.Whole.callEx correct ct fun a b h => ?_
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_, ca, wa, cb, wb⟩
    intro p hp
    rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2 p hp, h.2.2 p hp]
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono ((ready t hc.sp hs).wpF hc correct hd) fun _ hu => ⟨hu, trivial⟩

/-- A call's arguments, then the call. -/
theorem callWith_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {args : List (Reg × Value)} {k : Contract isa} {c : Prog isa} {name : String}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed25519.AArch64.Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true)
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ t, t.sp = L.E → Slots L args t →
      VG.Proof.Ed25519.AArch64.Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (callWith (setup args) name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb args hn hv hi hr ht).seq (call_ct correct ct hd ready kp hl)

/-! ## Each block and call -/

def zeroValues : List (Reg × Value) := [(.x15, .caller 2 0)]

theorem zeroStores_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (Slots L zeroValues)) (.block zeroStores)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have h15 : ∀ {t : State}, Slots L zeroValues t → t.gpr .x15 = L.scr := fun hs => by
    have h := hs (.x15, .caller 2 0) (by simp [zeroValues])
    simp only [argValue, Lay.value, BitVec.add_zero] at h
    exact h
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (RelCT.taint (A := taint) (Taint.ofRegs [.x15]) (fun a b h => ⟨h.1.1.sp.trans h.2.1.sp.symm,
      fun r hr => ?_⟩) (by taint_decide)) ?_ ?_
  · simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr
    rw [h15 h.1.2, h15 h.2.2]
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (zeroStores_ok hc (h15 hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem prune_ct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block prune)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc (h := Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114) rfl)
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
    (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine VG.Proof.Ed25519.AArch64.Whole.rel_wp
    (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
      (by taint_decide)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

def absorb_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L absorbValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.absorbAArch64 L.E L.inputs L.outputs t :=
  ⟨[L.SEED], [ST L, KS L], absorb_pre hL hsp hs, absorb_covers L, sponge_writes L⟩

def pad_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L padValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.padAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, KS L], pad_pre hL hsp hs, covers_writes (sponge_writes L), sponge_writes L⟩

def squeeze_ready (hL : L.Ok) {t : State} (hsp : t.sp = L.E) (hs : Slots L squeezeValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Sha3.squeezeAArch64 L.E L.inputs L.outputs t :=
  ⟨[], [ST L, HS L, KS L], squeeze_pre hL hsp hs, covers_writes (squeeze_writes L), squeeze_writes L⟩

def base_ready (hL : L.Ok) {t : State} (hs : Slots L baseValues t) :
    VG.Proof.Ed25519.AArch64.Whole.CallReady Proof.Ed448.AArch64.scalarBaseLocal L.E L.inputs L.outputs t :=
  ⟨[⟨L.E, 57⟩], L.outputs, base_pre hL hs, base_covers L, base_writes L⟩

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.BaseLadderOk) (hL : L.Ok)
    (ha : Arguments L m₁) (hb' : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (body v.callee)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have z := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb' zeroValues
    (by decide) (by simp [zeroValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [zeroValues])
    (by simp [zeroValues, preserved]) (by taint_decide)
  have a := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_absorb_scratch" ++ v.callee.suffix)
    hL ha hb' (args := absorbValues) (by decide)
    (by simp [absorbValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [absorbValues])
    (by simp [absorbValues, preserved]) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v)
    (Nat.le_of_eq v.absorb_depth) (fun _ hsp hs => absorb_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (by simp [absorbValues]),
      hg (.x1, .const 136) (by simp [absorbValues]), hg (.x2, .const 0) (by simp [absorbValues]),
      hg (.x3, .caller 1 0) (by simp [absorbValues]), hg (.x4, .const 57) (by simp [absorbValues]),
      hg (.x5, .caller 2 keccakScratch) (by simp [absorbValues]), hsp⟩)
    (by simp [absorbValues, linkRegs])
  have p := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_keccak_pad_scratch" ++ v.callee.suffix)
    hL ha hb' (args := padValues) (by decide)
    (by simp [padValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch]) (by simp [padValues])
    (by simp [padValues, preserved]) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (Nat.le_of_eq v.pad_depth) (fun _ hsp hs => pad_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (by simp [padValues]),
      hg (.x1, .const 136) (by simp [padValues]), hg (.x2, .const 57) (by simp [padValues]),
      hg (.x4, .caller 2 keccakScratch) (by simp [padValues]), hsp⟩)
    (by simp [padValues, linkRegs])
  have q := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (name := "vg_keccak_squeeze_scratch" ++ v.callee.suffix)
    hL ha hb' (args := squeezeValues) (by decide)
    (by simp [squeezeValues, VG.Proof.Ed25519.AArch64.Whole.valid, keccakScratch, hashAt])
    (by simp [squeezeValues]) (by simp [squeezeValues, preserved]) (by taint_decide)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v)
    (Nat.le_of_eq v.squeeze_depth) (fun _ hsp hs => squeeze_ready hL hsp hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hg (.x0, .caller 2 0) (by simp [squeezeValues]),
      hg (.x1, .const 136) (by simp [squeezeValues]), hg (.x2, .const 0) (by simp [squeezeValues]),
      hg (.x3, .frame hashAt) (by simp [squeezeValues]), hg (.x4, .const 114) (by simp [squeezeValues]),
      hg (.x5, .caller 2 keccakScratch) (by simp [squeezeValues]), hsp⟩)
    (by simp [squeezeValues, linkRegs])
  have b := callWith_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (name := "vg_ed448_scalar_base")
    hL ha hb' (args := baseValues) (by decide)
    (by simp [baseValues, VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp [baseValues])
    (by simp [baseValues, preserved]) (by taint_decide)
    (Proof.Ed448.AArch64.scalarBase_ok hb) Proof.Ed448.AArch64.scalarBase_ct
    (VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames base_noFrames) (fun _ _ hs => base_ready hL hs)
    (fun _ _ _ _ _ _ hsp hg => ⟨hsp, hg (.x0, .caller 0 0) (by simp [baseValues]),
      hg (.x1, .frame 0) (by simp [baseValues]), hg (.x2, .caller 2 0) (by simp [baseValues])⟩)
    (by simp [baseValues, linkRegs])
  exact (z.seq (zeroStores_ct.seq (a.seq (p.seq q)))).seq (prune_ct.seq (b.seq (wipe_ct hL)))

theorem lay_eq {s t : State} (hp : pkLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2]

theorem publicKey_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.BaseLadderOk) :
    ConstantTime isa pkLocal.pre pkLocal.pub (publicKeyWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hb (entry_ctx hs hp) (lay_ok hs) (entry_args hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    exact ⟨(body_ct v hb (lay_ok hs) (entry_args hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed448.publicKeyContract AArch64.abi 352) := by
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs]
    [satState] using satState

theorem publicKey_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.BaseLadderOk) :
    Verified AArch64.target (publicKeyWith v.callee) (Spec.Ed448.publicKeyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v hb h) (publicKey_ct v hb) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed448.AArch64.PublicKey
