/*
 * Copyright (c) 2007, 2008, Oracle and/or its affiliates. All rights reserved.
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

package sun.java2d.pipe.hw;

/**
 * An interface for receiving notifications about imminent accelerated device's
 * events. Upon receiving such event appropriate actions can be taken (for
 * example, resources associated with the device can be freed).
 */
public interface AccelDeviceEventListener {
    /**
     * Called when the device is about to be reset.
     *
     * One must release all native resources associated with the device which
     * prevent the device from being reset (such as Default Pool resources for
     * the D3D pipeline).
     *
     * It is safe to remove the listener while in the call back.
     *
     * Note: this method is called on the rendering thread,
     * do not call into user code, do not take RQ lock!
     */
    public void onDeviceReset();

    /**
     * Called when the device is about to be disposed of.
     *
     * One must release all native resources associated with the device.
     *
     * It is safe to remove the listener while in the call back.
     *
     * Note: this method is called on the rendering thread,
     * do not call into user code, do not take RQ lock!
     */
    public void onDeviceDispose();
}
