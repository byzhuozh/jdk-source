/*
 * Copyright (c) 2005, 2008, Oracle and/or its affiliates. All rights reserved.
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

package sun.management;

import java.lang.management.LockInfo;
import java.lang.management.ThreadInfo;
import javax.management.Attribute;
import javax.management.StandardMBean;
import javax.management.openmbean.CompositeData;

/**
 * This MXBean is used for data conversion from LockInfo
 * to CompositeData (its mapped type) or vice versa.
 */
class LockDataConverter extends StandardMBean
         implements LockDataConverterMXBean {
    private LockInfo      lockInfo;
    private LockInfo[]    lockedSyncs;

    LockDataConverter() {
        super(LockDataConverterMXBean.class, true);
        this.lockInfo = null;
        this.lockedSyncs = null;
    }

    LockDataConverter(ThreadInfo ti) {
        super(LockDataConverterMXBean.class, true);
        this.lockInfo = ti.getLockInfo();
        this.lockedSyncs = ti.getLockedSynchronizers();
    }

    public void setLockInfo(LockInfo l) {
        this.lockInfo = l;
    }

    public LockInfo getLockInfo() {
        return this.lockInfo;
    }

    public void setLockedSynchronizers(LockInfo[] l) {
        this.lockedSyncs = l;
    }

    public LockInfo[] getLockedSynchronizers() {
        return this.lockedSyncs;
    }

    // helper methods
    CompositeData toLockInfoCompositeData() {
        try {
            return (CompositeData) getAttribute("LockInfo");
        } catch (Exception e) {
            throw new AssertionError(e);
        }
    }

    CompositeData[] toLockedSynchronizersCompositeData() {
        try {
            return (CompositeData[]) getAttribute("LockedSynchronizers");
        } catch (Exception e) {
            throw new AssertionError(e);
        }
    }

    LockInfo toLockInfo(CompositeData cd) {
        try {
            setAttribute(new Attribute("LockInfo", cd));
        } catch (Exception e) {
            throw new AssertionError(e);
        }
        return getLockInfo();
    }

    LockInfo[] toLockedSynchronizers(CompositeData[] cd) {
        try {
            setAttribute(new Attribute("LockedSynchronizers", cd));
        } catch (Exception e) {
            throw new AssertionError(e);
        }
        return getLockedSynchronizers();
    }

    static CompositeData toLockInfoCompositeData(LockInfo l) {
        LockDataConverter ldc = new LockDataConverter();
        ldc.setLockInfo(l);
        return ldc.toLockInfoCompositeData();
    }
}
