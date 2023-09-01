{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedRecordDot #-}
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
import Data.Text (Text)
import qualified Data.Text.IO as Text.IO
import Metis.Asm.Class (MonadAsm)
import System.IO (Handle)

class (Monad m) => MonadLog m where
  trace :: Text -> m ()

instance (MonadLog m) => MonadLog (Control.Monad.State.Strict.StateT s m) where
  trace = lift . trace

instance (MonadLog m) => MonadLog (Control.Monad.State.Lazy.StateT s m) where
  trace = lift . trace

instance (MonadLog m) => MonadLog (Control.Monad.Reader.ReaderT r m) where
  trace = lift . trace

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

instance (MonadAsm isa m) => MonadAsm isa (HandleLoggingT m)

newtype NoLoggingT m a = NoLoggingT {value :: m a}
  deriving (Functor, Applicative, Monad, MonadFix)

noLogging :: NoLoggingT m a -> m a
noLogging ma = ma.value

instance MonadTrans NoLoggingT where
  lift = NoLoggingT

instance (Monad m) => MonadLog (NoLoggingT m) where
  trace _ = pure ()

instance (MonadAsm isa m) => MonadAsm isa (NoLoggingT m)