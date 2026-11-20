module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Shared
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.OpenTo
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Instance
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.MxCall
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Ssse3.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit

/-!
# ChaCha20-Poly1305 on x86-64: the functions as emitted

Each function over an implementation `v` of `vg_chacha20_xor`, followed by
the clearing of every register it may write and of its whole stack
(`Impl.ChaCha20Poly1305.X86_64.Fn`), meets its contract in constant time and
returns without secret residue. Its code is its code over a stub, with
`v`'s where it calls it (`Fill`), whose properties the kernel evaluates
once for each combination of `v.callee`'s `fold`, `pass`, `wide` and `vl`
with its `vg_poly1305_blocks` (`XorImpl.fold_poly`). The implementations of
`vg_poly1305_blocks` but the scalar one call `vg_mcdt_enter`, which loads
MXCSR: `X86_64.Scrub.mxCallsS` follows it there alone.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.ScrubFn

open VG VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Proof.ChaCha20.X86_64 (XorImpl)
open VG.Impl.ChaCha20.X86_64 (Callee)

/-- The level of the vector instructions of ChaCha20-Poly1305's code with
the implementation `b` of `vg_poly1305_blocks`, but those of the
implementation of `vg_chacha20_xor` it calls. -/
def polyLevel : Impl.Poly1305.X86_64.Blocks → VecLevel
  | .scalar => .sse
  | _ => .avx

/-- The level ChaCha20-Poly1305's functions over `v` clear their vector
registers at. -/
def cpLevel (v : XorImpl) : VecLevel := v.level.join (polyLevel v.poly)

/-- The combinations of `fold`, `pass` and `wide` of an implementation of
`vg_chacha20_xor` with the implementation `b` of `vg_poly1305_blocks` it
comes with (`XorImpl.fold_poly`). -/
abbrev Combo (fold pass wide : Nat) (b : Impl.Poly1305.X86_64.Blocks) : Prop :=
  (fold = 0 ∧ pass = 0 ∧ wide = 4 ∧ b = .scalar) ∨
    (fold = 448 ∧ pass = 0 ∧ wide = 5 ∧ b = .avx2) ∨
    (fold = 960 ∧ pass = 1024 ∧ wide = 6 ∧ (b = .avx512 ∨ b = .ifma))

/-! ## Without the cleanup -/

section
open VG.Impl.ChaCha20Poly1305.X86_64.Shared

/-- `seal`'s postcondition reads the memory on return only within the
buffers: the data and the tag. -/
theorem sealOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealContract abi stack) (Spec.ChaCha20Poly1305.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealPost_out _)

/-- `seal` of an instance, unscrubbed. -/
def sealPlain (v : XorImpl) : Unscrubbed Spec.ChaCha20Poly1305.sealApi X86_64.target where
  suffix := v.suffix
  code := sealCode v.callee v.poly
  verified := Shared.seal_verified v
  spSafe := Shared.seal_sp v

theorem openOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openZeroContract abi stack) (Spec.ChaCha20Poly1305.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (openZeroPost_out _)

def openPlain (v : XorImpl) : Unscrubbed Spec.ChaCha20Poly1305.openZeroApi X86_64.target where
  suffix := v.suffix
  code := openCode v.callee v.poly
  verified := Shared.open_verified v
  spSafe := Shared.open_sp v

theorem openToOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.openToContract abi stack) (Spec.ChaCha20Poly1305.openToSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain (openToPost_out _)

def openToPlain (v : XorImpl) : Unscrubbed Spec.ChaCha20Poly1305.openToApi X86_64.target where
  suffix := v.suffix
  code := Impl.ChaCha20Poly1305.X86_64.OpenTo.openToCode v.callee v.poly
  verified := OpenTo.openTo_verified v
  spSafe := OpenTo.openTo_sp v

/-- `seal_gather`'s postcondition reads the memory on return only within
`dst` and `tag`. -/
theorem sealGatherPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.ChaCha20Poly1305.sealGatherSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.ChaCha20Poly1305.sealGatherSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb) vs m m₁ r →
      Curry.apply (Spec.ChaCha20Poly1305.sealGatherSig.words pb) (Spec.ChaCha20Poly1305.sealGatherPost pb)
        vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 5
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.ChaCha20Poly1305.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
    ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr] (Spec.ChaCha20Poly1305.sealGatherPost pb) _ m m₂ r
  dsimp only [Curry.apply, Spec.ChaCha20Poly1305.sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro h₁ h₂
  rw [bytesAt_congr_len (p := dst) (agree_of hb.2.2.2.1), bytesAt_congr (p := tag) (agree_of hb.2.2.2.2)]
  exact h h₁ h₂

theorem gatherOut (stack : Nat) :
    PostOut (Spec.ChaCha20Poly1305.sealGatherContract abi stack)
      (Spec.ChaCha20Poly1305.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (sealGatherPost_out _)

def gatherPlain (v : XorImpl) : Unscrubbed Spec.ChaCha20Poly1305.sealGatherApi X86_64.target where
  suffix := v.suffix
  code := Gather.gatherCode v
  verified := Gather.gather_verified v
  spSafe := Gather.gather_spSafe v

end

theorem side_cp (v : XorImpl) : calleeSide v.callee.code (cpLevel v).level 16 = true :=
  calleeSide_mono (level_join_left _ _) (Nat.le_refl _) v.side

theorem poly_le (v : XorImpl) : (polyLevel v.poly).level ≤ (cpLevel v).level := level_join_right _ _

/-! ## `seal` -/

theorem seal_fillScalar {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.sealCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar)
      (Shared.sealCode ⟨name, code, 0, 0, 4, vl⟩ .scalar) := by
  cases vl <;> fill_calls_wide

theorem seal_stubScalar (vl : Bool) :
    stubSideM (Shared.sealCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar) (polyLevel .scalar).level (fun _ => 16) 1768 [] = true := by
  cases vl <;> lit_decide

theorem seal_fillAvx2 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.sealCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2)
      (Shared.sealCode ⟨name, code, 448, 0, 5, vl⟩ .avx2) := by
  cases vl <;> fill_calls_wide

theorem seal_stubAvx2 (vl : Bool) :
    stubSideM (Shared.sealCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2) (polyLevel .avx2).level (fun _ => 16) 1768 [] = true := by
  cases vl <;> lit_decide

theorem seal_fillAvx512 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.sealCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512)
      (Shared.sealCode ⟨name, code, 960, 1024, 6, vl⟩ .avx512) := by
  cases vl <;> fill_calls_wide

theorem seal_stubAvx512 (vl : Bool) :
    stubSideM (Shared.sealCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512) (polyLevel .avx512).level (fun _ => 16) 1768 [] = true := by
  cases vl <;> lit_decide

theorem seal_fillIfma {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.sealCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma)
      (Shared.sealCode ⟨name, code, 960, 1024, 6, vl⟩ .ifma) := by
  cases vl <;> fill_calls_wide

theorem seal_stubIfma (vl : Bool) :
    stubSideM (Shared.sealCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma) (polyLevel .ifma).level (fun _ => 16) 1768 [] = true := by
  cases vl <;> lit_decide

theorem seal_fill {k : Nat} (name : String) (code : Prog isa) (fold pass wide : Nat) (vl : Bool)
    (b : Impl.Poly1305.X86_64.Blocks) (hc : calleeSide code k 16 = true) (hp : Combo fold pass wide b) :
    Fill k (fun _ => 16) (Shared.sealCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (Shared.sealCode ⟨name, code, fold, pass, wide, vl⟩ b) := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact seal_fillScalar name code vl hc
  · exact seal_fillAvx2 name code vl hc
  · exact seal_fillAvx512 name code vl hc
  · exact seal_fillIfma name code vl hc

theorem seal_stub (fold pass wide : Nat) (vl : Bool) (b : Impl.Poly1305.X86_64.Blocks)
    (hp : Combo fold pass wide b) :
    stubSideM (Shared.sealCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (polyLevel b).level (fun _ => 16) 1768 [] = true := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact seal_stubScalar vl
  · exact seal_stubAvx2 vl
  · exact seal_stubAvx512 vl
  · exact seal_stubIfma vl

/-- `Spec.ChaCha20Poly1305.sealApi`'s function as emitted over `v`
(`Impl.ChaCha20Poly1305.X86_64.Fn.seal`) meets its contract in constant time
and returns without secret residue. -/
theorem seal_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Fn.seal (cpLevel v) v.callee v.poly)
      (Spec.ChaCha20Poly1305.sealApi.contract X86_64.abi 1768) 0 :=
  verifiedScrubbedAllFillM (sealPlain v) (cpLevel v) (sealOut _)
    (seal_fill v.callee.name v.callee.code _ _ _ v.callee.vl v.poly (side_cp v) v.fold_poly)
    (poly_le v) (Nat.le_refl _)
    (ha := seal_stub _ _ _ v.callee.vl v.poly v.fold_poly)

theorem seal_spSafeFn (v : XorImpl) :
    (Fn.seal (cpLevel v) v.callee v.poly).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Shared.seal_sp v)

/-! ## `open` -/

theorem open_fillScalar {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.openCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar)
      (Shared.openCode ⟨name, code, 0, 0, 4, vl⟩ .scalar) := by
  cases vl <;> fill_calls_wide

theorem open_stubScalar (vl : Bool) :
    stubSideM (Shared.openCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar) (polyLevel .scalar).level (fun _ => 16) 1784 [] = true := by
  cases vl <;> lit_decide

theorem open_fillAvx2 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.openCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2)
      (Shared.openCode ⟨name, code, 448, 0, 5, vl⟩ .avx2) := by
  cases vl <;> fill_calls_wide

theorem open_stubAvx2 (vl : Bool) :
    stubSideM (Shared.openCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2) (polyLevel .avx2).level (fun _ => 16) 1784 [] = true := by
  cases vl <;> lit_decide

theorem open_fillAvx512 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.openCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512)
      (Shared.openCode ⟨name, code, 960, 1024, 6, vl⟩ .avx512) := by
  cases vl <;> fill_calls_wide

theorem open_stubAvx512 (vl : Bool) :
    stubSideM (Shared.openCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512) (polyLevel .avx512).level (fun _ => 16) 1784 [] = true := by
  cases vl <;> lit_decide

theorem open_fillIfma {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Shared.openCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma)
      (Shared.openCode ⟨name, code, 960, 1024, 6, vl⟩ .ifma) := by
  cases vl <;> fill_calls_wide

theorem open_stubIfma (vl : Bool) :
    stubSideM (Shared.openCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma) (polyLevel .ifma).level (fun _ => 16) 1784 [] = true := by
  cases vl <;> lit_decide

theorem open_fill {k : Nat} (name : String) (code : Prog isa) (fold pass wide : Nat) (vl : Bool)
    (b : Impl.Poly1305.X86_64.Blocks) (hc : calleeSide code k 16 = true) (hp : Combo fold pass wide b) :
    Fill k (fun _ => 16) (Shared.openCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (Shared.openCode ⟨name, code, fold, pass, wide, vl⟩ b) := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact open_fillScalar name code vl hc
  · exact open_fillAvx2 name code vl hc
  · exact open_fillAvx512 name code vl hc
  · exact open_fillIfma name code vl hc

theorem open_stub (fold pass wide : Nat) (vl : Bool) (b : Impl.Poly1305.X86_64.Blocks)
    (hp : Combo fold pass wide b) :
    stubSideM (Shared.openCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (polyLevel b).level (fun _ => 16) 1784 [] = true := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact open_stubScalar vl
  · exact open_stubAvx2 vl
  · exact open_stubAvx512 vl
  · exact open_stubIfma vl

/-- `Spec.ChaCha20Poly1305.openZeroApi`'s function as emitted over `v`
(`Impl.ChaCha20Poly1305.X86_64.Fn.open`) meets its contract in constant time
and returns without secret residue. -/
theorem open_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Fn.open (cpLevel v) v.callee v.poly)
      (Spec.ChaCha20Poly1305.openZeroApi.contract X86_64.abi 1784) 32 :=
  verifiedScrubbedAllFillM (openPlain v) (cpLevel v) (openOut _)
    (open_fill v.callee.name v.callee.code _ _ _ v.callee.vl v.poly (side_cp v) v.fold_poly)
    (poly_le v) (Nat.le_refl _)
    (ha := open_stub _ _ _ v.callee.vl v.poly v.fold_poly)

theorem open_spSafeFn (v : XorImpl) :
    (Fn.open (cpLevel v) v.callee v.poly).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Shared.open_sp v)

/-! ## `openTo` -/

theorem openTo_fillScalar {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (OpenTo.openToCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar)
      (OpenTo.openToCode ⟨name, code, 0, 0, 4, vl⟩ .scalar) := by
  cases vl <;> fill_calls_wide

theorem openTo_stubScalar (vl : Bool) :
    stubSideM (OpenTo.openToCode ⟨"", .block [], 0, 0, 4, vl⟩ .scalar) (polyLevel .scalar).level (fun _ => 16) 1800 [] = true := by
  cases vl <;> lit_decide

theorem openTo_fillAvx2 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (OpenTo.openToCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2)
      (OpenTo.openToCode ⟨name, code, 448, 0, 5, vl⟩ .avx2) := by
  cases vl <;> fill_calls_wide

theorem openTo_stubAvx2 (vl : Bool) :
    stubSideM (OpenTo.openToCode ⟨"", .block [], 448, 0, 5, vl⟩ .avx2) (polyLevel .avx2).level (fun _ => 16) 1800 [] = true := by
  cases vl <;> lit_decide

theorem openTo_fillAvx512 {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (OpenTo.openToCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512)
      (OpenTo.openToCode ⟨name, code, 960, 1024, 6, vl⟩ .avx512) := by
  cases vl <;> fill_calls_wide

theorem openTo_stubAvx512 (vl : Bool) :
    stubSideM (OpenTo.openToCode ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512) (polyLevel .avx512).level (fun _ => 16) 1800 [] = true := by
  cases vl <;> lit_decide

theorem openTo_fillIfma {k : Nat} (name : String) (code : Prog isa) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (OpenTo.openToCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma)
      (OpenTo.openToCode ⟨name, code, 960, 1024, 6, vl⟩ .ifma) := by
  cases vl <;> fill_calls_wide

theorem openTo_stubIfma (vl : Bool) :
    stubSideM (OpenTo.openToCode ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma) (polyLevel .ifma).level (fun _ => 16) 1800 [] = true := by
  cases vl <;> lit_decide

theorem openTo_fill {k : Nat} (name : String) (code : Prog isa) (fold pass wide : Nat) (vl : Bool)
    (b : Impl.Poly1305.X86_64.Blocks) (hc : calleeSide code k 16 = true) (hp : Combo fold pass wide b) :
    Fill k (fun _ => 16) (OpenTo.openToCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (OpenTo.openToCode ⟨name, code, fold, pass, wide, vl⟩ b) := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact openTo_fillScalar name code vl hc
  · exact openTo_fillAvx2 name code vl hc
  · exact openTo_fillAvx512 name code vl hc
  · exact openTo_fillIfma name code vl hc

theorem openTo_stub (fold pass wide : Nat) (vl : Bool) (b : Impl.Poly1305.X86_64.Blocks)
    (hp : Combo fold pass wide b) :
    stubSideM (OpenTo.openToCode ⟨"", .block [], fold, pass, wide, vl⟩ b) (polyLevel b).level (fun _ => 16) 1800 [] = true := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact openTo_stubScalar vl
  · exact openTo_stubAvx2 vl
  · exact openTo_stubAvx512 vl
  · exact openTo_stubIfma vl

/-- `Spec.ChaCha20Poly1305.openToApi`'s function as emitted over `v`
(`Impl.ChaCha20Poly1305.X86_64.Fn.openTo`) meets its contract in constant time
and returns without secret residue. -/
theorem openTo_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Fn.openTo (cpLevel v) v.callee v.poly)
      (Spec.ChaCha20Poly1305.openToApi.contract X86_64.abi 1800) 32 :=
  verifiedScrubbedAllFillM (openToPlain v) (cpLevel v) (openToOut _)
    (openTo_fill v.callee.name v.callee.code _ _ _ v.callee.vl v.poly (side_cp v) v.fold_poly)
    (poly_le v) (Nat.le_refl _)
    (ha := openTo_stub _ _ _ v.callee.vl v.poly v.fold_poly)

theorem openTo_spSafeFn (v : XorImpl) :
    (Fn.openTo (cpLevel v) v.callee v.poly).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (OpenTo.openTo_sp v)

/-! ## `seal_gather` -/

/-- The name of `seal`'s code without its cleanup, which `seal_gather` over
`v` calls. -/
def sealName (v : XorImpl) : String := (Gather.Whole.sealFn v).name

/-- The name of `seal_split`'s code over `v`, which `seal_gather` calls. -/
def splitName (v : XorImpl) : String := (Gather.sealSplitFn v).name

theorem gatherCode_eq (v : XorImpl) :
    Gather.gatherCode v = Fn.gatherCode (sealName v) (splitName v) v.callee v.poly := by
  unfold Gather.gatherCode
  simp only [sealName, splitName, Gather.Whole.sealFn, Gather.sealSplitFn, Gather.width]
  generalize v.poly = b
  cases b <;> rfl

theorem gather_fillScalar {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 0, 0, 4, vl⟩ .scalar)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 0, 0, 4, vl⟩ .scalar) := by
  cases vl <;> fill_calls_wide

theorem gather_stubScalar (vl : Bool) :
    stubSideM (Fn.gatherCode "" "" ⟨"", .block [], 0, 0, 4, vl⟩ .scalar) (polyLevel .scalar).level (fun _ => 16) 1880 [] = true := by
  cases vl <;> lit_decide

theorem gather_fillAvx2 {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 448, 0, 5, vl⟩ .avx2)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 448, 0, 5, vl⟩ .avx2) := by
  cases vl <;> fill_calls_wide

theorem gather_stubAvx2 (vl : Bool) :
    stubSideM (Fn.gatherCode "" "" ⟨"", .block [], 448, 0, 5, vl⟩ .avx2) (polyLevel .avx2).level (fun _ => 16) 1880 [] = true := by
  cases vl <;> lit_decide

theorem gather_fillAvx512F {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, false⟩ .avx512)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 960, 1024, 6, false⟩ .avx512) := by
  fill_calls_wide

theorem gather_fillAvx512T {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, true⟩ .avx512)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 960, 1024, 6, true⟩ .avx512) := by
  fill_calls_wide

theorem gather_fillAvx512 {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 960, 1024, 6, vl⟩ .avx512) := by
  cases vl
  · exact gather_fillAvx512F name code n₁ n₂ hc
  · exact gather_fillAvx512T name code n₁ n₂ hc

theorem gather_stubAvx512 (vl : Bool) :
    stubSideM (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, vl⟩ .avx512) (polyLevel .avx512).level (fun _ => 16) 1880 [] = true := by
  cases vl <;> lit_decide

theorem gather_fillIfma {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String) (vl : Bool)
    (hc : calleeSide code k 16 = true) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma)
      (Fn.gatherCode n₁ n₂ ⟨name, code, 960, 1024, 6, vl⟩ .ifma) := by
  cases vl <;> fill_calls_wide

theorem gather_stubIfma (vl : Bool) :
    stubSideM (Fn.gatherCode "" "" ⟨"", .block [], 960, 1024, 6, vl⟩ .ifma) (polyLevel .ifma).level (fun _ => 16) 1880 [] = true := by
  cases vl <;> lit_decide

theorem gather_fill {k : Nat} (name : String) (code : Prog isa) (n₁ n₂ : String) (fold pass wide : Nat) (vl : Bool)
    (b : Impl.Poly1305.X86_64.Blocks) (hc : calleeSide code k 16 = true) (hp : Combo fold pass wide b) :
    Fill k (fun _ => 16) (Fn.gatherCode "" "" ⟨"", .block [], fold, pass, wide, vl⟩ b) (Fn.gatherCode n₁ n₂ ⟨name, code, fold, pass, wide, vl⟩ b) := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact gather_fillScalar name code n₁ n₂ vl hc
  · exact gather_fillAvx2 name code n₁ n₂ vl hc
  · exact gather_fillAvx512 name code n₁ n₂ vl hc
  · exact gather_fillIfma name code n₁ n₂ vl hc

theorem gather_stub (fold pass wide : Nat) (vl : Bool) (b : Impl.Poly1305.X86_64.Blocks)
    (hp : Combo fold pass wide b) :
    stubSideM (Fn.gatherCode "" "" ⟨"", .block [], fold, pass, wide, vl⟩ b) (polyLevel b).level (fun _ => 16) 1880 [] = true := by
  rcases hp with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl | rfl⟩
  · exact gather_stubScalar vl
  · exact gather_stubAvx2 vl
  · exact gather_stubAvx512 vl
  · exact gather_stubIfma vl

/-- `Spec.ChaCha20Poly1305.sealGatherApi`'s function as emitted over `v`
(`Impl.ChaCha20Poly1305.X86_64.Fn.sealGather`) meets its contract in
constant time and returns without secret residue. -/
theorem gather_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Fn.sealGather (cpLevel v) (sealName v) (splitName v) v.callee v.poly)
      (Spec.ChaCha20Poly1305.sealGatherApi.contract X86_64.abi 1880) 0 := by
  have hf : Fill (cpLevel v).level (fun _ => 16)
      (Fn.gatherCode "" "" ⟨"", .block [], v.callee.fold, v.callee.pass, v.callee.wide, v.callee.vl⟩ v.poly)
      (gatherPlain v).code := by
    show Fill _ _ _ (Gather.gatherCode v)
    rw [gatherCode_eq]
    exact gather_fill v.callee.name v.callee.code (sealName v) (splitName v) _ _ _ v.callee.vl v.poly
      (side_cp v) v.fold_poly
  have e : Fn.sealGather (cpLevel v) (sealName v) (splitName v) v.callee v.poly =
      scrubAll (cpLevel v) 0 1880 (gatherPlain v).code := by
    unfold Fn.sealGather
    rw [← gatherCode_eq]
    rfl
  rw [e]
  exact verifiedScrubbedAllFillM (gatherPlain v) (cpLevel v) (gatherOut _) hf
    (poly_le v) (Nat.le_refl _) (ha := gather_stub _ _ _ v.callee.vl v.poly v.fold_poly)

theorem gather_spSafeFn (v : XorImpl) :
    (Fn.sealGather (cpLevel v) (sealName v) (splitName v) v.callee v.poly).all
      (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold Fn.sealGather
  rw [← gatherCode_eq]
  exact scrubKs_spSafe (Gather.gather_spSafe v)

end VG.Proof.ChaCha20Poly1305.X86_64.ScrubFn
