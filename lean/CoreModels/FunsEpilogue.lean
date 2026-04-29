import CoreModels.Alloc.Funs

namespace CoreModels

/-! ## `[T]::to_vec` and `Box<[T]>::into_vec`

Aeneas's builtin name map turns `<[T]>::to_vec` into a reference to
`alloc.slice.Slice.to_vec` (and similarly for `into_vec`). Our local
`alloc/` crate provides those bodies, but under the `alloc.slice.Dummy`
namespace because of the standard "you can't `impl` for a foreign slice
type" workaround. Re-export them at the std-map name so downstream
extractions land on a defined symbol.
-/

noncomputable section

@[rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Aeneas.Std.Slice T) :
  Aeneas.Std.Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.to_vec cloneInst s

@[rust_fun "alloc::slice::{alloc::boxed::Box<[@T], @A>}::into_vec"]
def alloc.slice.Slice.into_vec
  {T : Type} (A : Type) (s : Aeneas.Std.Slice T) : Aeneas.Std.Result (alloc.vec.Vec T) :=
  alloc.slice.Dummy.into_vec A s

end

/-! ## Renaming `From` instances
  Aeneas extracts `i64::from()` as `core.convert.num.FromI64I32.from`, so we need to redirect here:
-/

abbrev core.convert.num.FromU16U8.from    := U16.Insts.Core_modelsConvertFromU8.from
abbrev core.convert.num.FromU32U8.from    := U32.Insts.Core_modelsConvertFromU8.from
abbrev core.convert.num.FromU32U16.from   := U32.Insts.Core_modelsConvertFromU16.from
abbrev core.convert.num.FromU64U8.from    := U64.Insts.Core_modelsConvertFromU8.from
abbrev core.convert.num.FromU64U16.from   := U64.Insts.Core_modelsConvertFromU16.from
abbrev core.convert.num.FromU64U32.from   := U64.Insts.Core_modelsConvertFromU32.from
abbrev core.convert.num.FromU128U8.from   := U128.Insts.Core_modelsConvertFromU8.from
abbrev core.convert.num.FromU128U16.from  := U128.Insts.Core_modelsConvertFromU16.from
abbrev core.convert.num.FromU128U32.from  := U128.Insts.Core_modelsConvertFromU32.from
abbrev core.convert.num.FromU128U64.from  := U128.Insts.Core_modelsConvertFromU64.from
abbrev core.convert.num.FromU128Usize.from := U128.Insts.Core_modelsConvertFromUsize.from
abbrev core.convert.num.FromUsizeU8.from  := Usize.Insts.Core_modelsConvertFromU8.from
abbrev core.convert.num.FromUsizeU16.from := Usize.Insts.Core_modelsConvertFromU16.from
abbrev core.convert.num.FromI16I8.from    := I16.Insts.Core_modelsConvertFromI8.from
abbrev core.convert.num.FromI32I8.from    := I32.Insts.Core_modelsConvertFromI8.from
abbrev core.convert.num.FromI32I16.from   := I32.Insts.Core_modelsConvertFromI16.from
abbrev core.convert.num.FromI64I8.from    := I64.Insts.Core_modelsConvertFromI8.from
abbrev core.convert.num.FromI64I16.from   := I64.Insts.Core_modelsConvertFromI16.from
abbrev core.convert.num.FromI64I32.from   := I64.Insts.Core_modelsConvertFromI32.from
abbrev core.convert.num.FromI128I8.from   := I128.Insts.Core_modelsConvertFromI8.from
abbrev core.convert.num.FromI128I16.from  := I128.Insts.Core_modelsConvertFromI16.from
abbrev core.convert.num.FromI128I32.from  := I128.Insts.Core_modelsConvertFromI32.from
abbrev core.convert.num.FromI128I64.from  := I128.Insts.Core_modelsConvertFromI64.from
abbrev core.convert.num.FromI128Isize.from := I128.Insts.Core_modelsConvertFromIsize.from
abbrev core.convert.num.FromIsizeI8.from  := Isize.Insts.Core_modelsConvertFromI8.from
abbrev core.convert.num.FromIsizeI16.from := Isize.Insts.Core_modelsConvertFromI16.from

end CoreModels
