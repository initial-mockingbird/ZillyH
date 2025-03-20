{-# LANGUAGE LinearTypes #-}
module Fun where


newtype Ctx = Ctx {getCtx :: Int}

data App = App 
  { fun :: App 
  , arg :: App
  }

foo :: App -> Ctx -> App
foo (App fun arg) ctx = App (foo fun ctx) (foo arg ctx)

foo' :: App -> Ctx -> (Ctx, App)
foo' (App fun arg) ctx0 = case foo' fun ctx0 of
  (ctx1, fun') -> case foo' arg ctx1 of
    (ctx2, arg') -> (ctx2, App fun' arg')

foo'' :: App -> Ctx -> (Ctx, App)
foo'' (App fun arg) ctx0 =
  let (ctx1, fun') = foo'' fun ctx0 in
  let (ctx2, arg') = foo'' arg ctx1 in
  (ctx2, App fun' arg')



