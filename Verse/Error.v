Definition optionToError {A E : Type}(e : E)(op : option A)
: match op with
    | None   => E
    | Some _ => A
  end :=
  match op with
    | None   => e
    | Some x => x
  end.
