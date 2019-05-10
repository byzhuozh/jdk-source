/*
 * Copyright (c) 2003, 2011, Oracle and/or its affiliates. All rights reserved.
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

import com.sun.management.GarbageCollectorMXBean;
import com.sun.management.GarbageCollectionNotificationInfo;
import java.lang.management.ManagementFactory;
import java.lang.management.MemoryPoolMXBean;
import java.lang.management.MemoryUsage;

import com.sun.management.GcInfo;
import javax.management.openmbean.CompositeData;
import javax.management.MBeanInfo;
import javax.management.MBeanAttributeInfo;
import javax.management.ObjectName;
import javax.management.MBeanNotificationInfo;
import javax.management.Notification;
import javax.management.NotificationFilter;
import javax.management.NotificationListener;
import javax.management.ListenerNotFoundException;

import java.util.List;
import java.util.ListIterator;
import java.util.Map;

/**
 * Implementation class for the garbage collector.
 * Standard and committed hotspot-specific metrics if any.
 *
 * ManagementFactory.getGarbageCollectorMXBeans() returns a list
 * of instances of this class.
 */
class GarbageCollectorImpl extends MemoryManagerImpl
    implements GarbageCollectorMXBean {

    GarbageCollectorImpl(String name) {
        super(name);
    }

    public native long getCollectionCount();
    public native long getCollectionTime();


    // The memory pools are static and won't be changed.
    // TODO: If the hotspot implementation begins to have pools
    // dynamically created and removed, this needs to be modified.
    private String[] poolNames = null;
    synchronized String[] getAllPoolNames() {
        if (poolNames == null) {
            List pools = ManagementFactory.getMemoryPoolMXBeans();
            poolNames = new String[pools.size()];
            int i = 0;
            for (ListIterator iter = pools.listIterator();
                 iter.hasNext();
                 i++) {
                MemoryPoolMXBean p = (MemoryPoolMXBean) iter.next();
                poolNames[i] = p.getName();
            }
        }
        return poolNames;
    }

    // Sun JDK extension
    private GcInfoBuilder gcInfoBuilder;

    private synchronized GcInfoBuilder getGcInfoBuilder() {
        if(gcInfoBuilder == null) {
            gcInfoBuilder = new GcInfoBuilder(this, getAllPoolNames());
        }
        return gcInfoBuilder;
    }

    public GcInfo getLastGcInfo() {
        GcInfo info = getGcInfoBuilder().getLastGcInfo();
        return info;
    }

    private final static String notifName =
        "javax.management.Notification";

    private final static String[] gcNotifTypes = {
        GarbageCollectionNotificationInfo.GARBAGE_COLLECTION_NOTIFICATION
    };

    private MBeanNotificationInfo[] notifInfo = null;
    public MBeanNotificationInfo[] getNotificationInfo() {
        synchronized (this) {
            if (notifInfo == null) {
                 notifInfo = new MBeanNotificationInfo[1];
                 notifInfo[0] = new MBeanNotificationInfo(gcNotifTypes,
                                                          notifName,
                                                          "GC Notification");
            }
        }
        return notifInfo;
    }

    private static long seqNumber = 0;
    private static long getNextSeqNumber() {
        return ++seqNumber;
    }

    void createGCNotification(long timestamp,
                              String gcName,
                              String gcAction,
                              String gcCause,
                              GcInfo gcInfo)  {

        if (!hasListeners()) {
            return;
        }

        Notification notif = new Notification(GarbageCollectionNotificationInfo.GARBAGE_COLLECTION_NOTIFICATION,
                                              getObjectName(),
                                              getNextSeqNumber(),
                                              timestamp,
                                              gcName);
        GarbageCollectionNotificationInfo info =
            new GarbageCollectionNotificationInfo(gcName,
                                                  gcAction,
                                                  gcCause,
                                                  gcInfo);

        CompositeData cd =
            GarbageCollectionNotifInfoCompositeData.toCompositeData(info);
        notif.setUserData(cd);
        sendNotification(notif);
    }

    public synchronized void addNotificationListener(NotificationListener listener,
                                                     NotificationFilter filter,
                                                     Object handback)
    {
        boolean before = hasListeners();
        super.addNotificationListener(listener, filter, handback);
        boolean after = hasListeners();
        if (!before && after) {
            setNotificationEnabled(this, true);
        }
    }

    public synchronized void removeNotificationListener(NotificationListener listener)
        throws ListenerNotFoundException {
        boolean before = hasListeners();
        super.removeNotificationListener(listener);
        boolean after = hasListeners();
        if (before && !after) {
            setNotificationEnabled(this,false);
        }
    }

    public synchronized void removeNotificationListener(NotificationListener listener,
                                                        NotificationFilter filter,
                                                        Object handback)
            throws ListenerNotFoundException
    {
        boolean before = hasListeners();
        super.removeNotificationListener(listener,filter,handback);
        boolean after = hasListeners();
        if (before && !after) {
            setNotificationEnabled(this,false);
        }
    }

    public ObjectName getObjectName() {
        return Util.newObjectName(ManagementFactory.GARBAGE_COLLECTOR_MXBEAN_DOMAIN_TYPE, getName());
    }

    native void setNotificationEnabled(GarbageCollectorMXBean gc,
                                       boolean enabled);

}
