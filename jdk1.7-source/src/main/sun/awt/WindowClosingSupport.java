/*
 * Copyright (c) 1999, 2007, Oracle and/or its affiliates. All rights reserved.
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

/**
 * Interface for identifying and casting toolkits that support
 * WindowClosingListeners.
 */
public interface WindowClosingSupport {
    WindowClosingListener getWindowClosingListener();
    void setWindowClosingListener(WindowClosingListener wcl);
}
