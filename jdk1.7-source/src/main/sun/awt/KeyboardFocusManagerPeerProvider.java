/*
 * Copyright (c) 2007, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.awt;

import java.awt.KeyboardFocusManager;
import java.awt.peer.KeyboardFocusManagerPeer;

/**
 * {@link KeyboardFocusManagerPeerProvider} is required to be implemented by
 * the currently used {@link java.awt.Toolkit} instance. In order to initialize
 * {@link java.awt.KeyboardFocusManager}, an instance of {@link KeyboardFocusManagerPeer}
 * is needed. To create that instance, the {@link #createKeyboardFocusManagerPeer}
 * method of the current toolkit is called.
 */
public interface KeyboardFocusManagerPeerProvider {

    /**
     * Creates a KeyboardFocusManagerPeer for the specified KeyboardFocusManager.
     */
    KeyboardFocusManagerPeer createKeyboardFocusManagerPeer(KeyboardFocusManager manager);
}
