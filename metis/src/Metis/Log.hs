{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Metis.Log (
  MonadLog (..),
  HandleLoggingT,
  handleLogging,
  NoLoggingT,
  noLogging,
) where

import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (ask)
import qualified Control.Monad.State.Lazy
import qualified Control.Monad.State.Strict
import Control.Monad.Trans.Class (MonadTrans, lift)
import qualified Control.Monad.Writer.CPS
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import qualified Metis.Asm.Class
import qualified Metis.Asm.ClassNew
import System.IO (Handle)

class (Monad m) => MonadLog m where
  trace :: Text -> m ()
  default trace :: (m ~ t n, MonadTrans t, MonadLog n) => Text -> m ()
  trace = lift . trace

instance (MonadLog m) => MonadLog (Control.Monad.State.Strict.StateT s m)

instance (MonadLog m) => MonadLog (Control.Monad.State.Lazy.StateT s m)

instance (MonadLog m) => MonadLog (Control.Monad.Reader.ReaderT r m)

instance (MonadLog m) => MonadLog (Control.Monad.Writer.CPS.WriterT r m)

newtype HandleLoggingT m a = HandleLoggingT {value :: ReaderT Handle m a}
  deriving (Functor, Applicative, Monad, MonadFix)

handleLogging :: Handle -> HandleLoggingT m a -> m a
handleLogging handle ma = runReaderT ma.value handle

instance MonadTrans HandleLoggingT where
  lift = HandleLoggingT . lift

instance (MonadIO m) => MonadLog (HandleLoggingT m) where
  trace s = HandleLoggingT $ do
    handle <- ask
    liftIO $ Text.IO.hPutStrLn handle s

instance (Metis.Asm.Class.MonadAsm isa m) => Metis.Asm.Class.MonadAsm isa (HandleLoggingT m)
instance (Metis.Asm.ClassNew.MonadAsm isa m) => Metis.Asm.ClassNew.MonadAsm isa (HandleLoggingT m)

newtype NoLoggingT m a = NoLoggingT {value :: m a}
  deriving (Functor, Applicative, Monad, MonadFix)

noLogging :: NoLoggingT m a -> m a
noLogging ma = ma.value

instance MonadTrans NoLoggingT where
  lift = NoLoggingT

instance (Monad m) => MonadLog (NoLoggingT m) where
  trace _ = pure ()

instance (Metis.Asm.Class.MonadAsm isa m) => Metis.Asm.Class.MonadAsm isa (NoLoggingT m)
instance (Metis.Asm.ClassNew.MonadAsm isa m) => Metis.Asm.ClassNew.MonadAsm isa (NoLoggingT m)