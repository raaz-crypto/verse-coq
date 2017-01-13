

Definition statements := list statement.

Definition varSpec    := sigT var.
Definition context    := list varSpec.

Record function : Type
  := makeFunction { name    : string;
                    params  : context;
                    locals  : context; 
                    body    : statements;
                  }.
